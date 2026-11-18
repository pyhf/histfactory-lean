import HistFactory.Trusted

namespace HistFactory

open Number
variable {K : Type} [Number K] {n : Nat}

/-- Keeps, for every key, the first element with that key. -/
def firstBy {α κ : Type} [DecidableEq κ] (key : α → κ) : List α → List α
  | [] => []
  | a :: rest => a :: (firstBy key rest).filter (key · ≠ key a)

/-! ## 1. Parameter sets -/

deriving instance DecidableEq, Repr for Sharing

/-- The family of a constraint, without its numbers. -/
inductive Kind
  | free
  | normal
  | poisson
  deriving DecidableEq, Repr

def ConstraintSpec.kind : ConstraintSpec K n → Kind
  | .free => .free
  | .normal _ _ => .normal
  | .mcStat _ => .normal
  | .poisson _ => .poisson

/-- The requirement of a modifier on its parameter set. -/
def Modifier.paramSpec (nom : Fin n → K) (m : Modifier K n) : ParamSpec K n :=
  (m.effect.spec nom).paramspec

/-- A named group of parameters: the part of a requirement that contains no numbers,
so that two of them can be compared. -/
structure ParamSet where
  name : String
  size : Nat
  kind : Kind
  sharing : Sharing
  deriving DecidableEq, Repr

/-- The parameter set a modifier asks for. -/
def Modifier.paramSet (nom : Fin n → K) (m : Modifier K n) : ParamSet :=
  let spec := m.paramSpec nom
  ⟨m.parameset, spec.shape.size n, spec.constraint.kind, spec.sharing⟩

/-- The parameter sets of a model, one per name, in order of first appearance. -/
def Model.paramSets (m : Model K) : List ParamSet :=
  firstBy ParamSet.name <|
    m.channels.flatMap fun c => c.samples.flatMap fun s =>
      s.modifiers.map (·.paramSet s.nominal)

/-- The total number of parameters. -/
def Model.size (m : Model K) : Nat :=
  (m.paramSets.map (·.size)).sum

/-! ## 2. Constraint terms -/

/-- One auxiliary measurement of the parameter `name[index]`: a Gaussian one with its
nominal value and width, or a Poisson one with its nominal count `tau`. -/
inductive Constraint (K : Type)
  | gaus (name : String) (index : Nat) (observed width : K)
  | pois (name : String) (index : Nat) (tau : K)

/-- The parameter a constraint term belongs to. -/
def Constraint.param : Constraint K → String × Nat
  | .gaus p i _ _ => (p, i)
  | .pois p i _ => (p, i)

/-- The nominal value of the auxiliary measurement. -/
def Constraint.observed : Constraint K → K
  | .gaus _ _ a _ => a
  | .pois _ _ τ => τ

/-- For bin `b`: nominal rate and absolute uncertainty of every sample of the channel that
has a `staterror` on the parameter `name`. -/
def Channel.mcStat (c : Channel K) (name : String) (b : Fin c.bins) : List (K × K) :=
  c.samples.flatMap fun s => s.modifiers.filterMap fun m =>
    match (m.paramSpec s.nominal).constraint with
    | .mcStat unc => if m.parameset = name then some (s.nominal b, unc b) else none
    | .free | .normal _ _ | .poisson _ => none

/-- Relative Monte Carlo statistical uncertainty of bin `b`: the uncertainties of the
contributing samples added in quadrature, over their total nominal rate. -/
def Channel.mcWidth (c : Channel K) (name : String) (b : Fin c.bins) : K :=
  sqrt ((c.mcStat name b).map (·.2 ^ 2)).sum / ((c.mcStat name b).map (·.1)).sum

/-- The constraint terms a requirement implies for the parameter `p` in channel `c`. -/
def ConstraintSpec.terms (c : Channel K) (p : String) :
    ConstraintSpec K c.bins → List (Constraint K)
  | .free => []
  | .normal aux sigma => [.gaus p 0 aux sigma]
  | .mcStat _ => List.ofFn fun b : Fin c.bins => .gaus p b 1 (c.mcWidth p b)
  | .poisson tau => List.ofFn fun b : Fin c.bins => .pois p b (tau b)

def Modifier.constraints (c : Channel K) (s : Sample K c.bins) (m : Modifier K c.bins) :
    List (Constraint K) :=
  (m.paramSpec s.nominal).constraint.terms c m.parameset

/-- The constraint terms of a model, one per parameter, in order of first appearance. -/
def Model.constraints (m : Model K) : List (Constraint K) :=
  firstBy Constraint.param <|
    m.channels.flatMap fun c => c.samples.flatMap fun s =>
      s.modifiers.flatMap (·.constraints c s)

/-- The constraint term of the parameter `name[i]`, if it has one. -/
def Model.constraintFor (m : Model K) (name : String) (i : Nat) : Option (Constraint K) :=
  m.constraints.find? (·.param = (name, i))

/-! ## 3. Data -/

/-- A table from rows `(name, values)`. A missing entry reads as 0. -/
def Table.ofList (rows : List (String × List K)) : Table K :=
  fun name i => ((rows.lookup name).getD []).getD i 0

def ParameterTable.ofList (rows : List (String × List K)) : ParameterTable K :=
  ⟨Table.ofList rows⟩

/-- Observed counts, by channel name and bin. -/
structure ObservedData (K : Type) where
  values : Table K

def ObservedData.ofList (rows : List (String × List K)) : ObservedData K :=
  ⟨Table.ofList rows⟩

/-- Auxiliary data, by parameter name and index. -/
structure ConstraintData (K : Type) where
  values : Table K

/-- Everything the likelihood is evaluated on. -/
structure Data (K : Type) where
  counts : ObservedData K
  aux : ConstraintData K

/-- The auxiliary data of the model itself: the nominal value of every constraint term. -/
def Model.auxdata (m : Model K) : ConstraintData K :=
  ⟨fun name i =>
    match m.constraintFor name i with
    | some k => k.observed
    | none => 0⟩

/-- Observed counts together with the auxiliary data of the model. -/
def Model.observed (m : Model K) (counts : List (String × List K)) : Data K :=
  ⟨.ofList counts, m.auxdata⟩

/-- The requirements of all modifiers on the parameter set `name`, in order of appearance. -/
def Model.paramSpecs (m : Model K) (name : String) : List (Σ n, ParamSpec K n) :=
  m.channels.flatMap fun c => c.samples.flatMap fun s => s.modifiers.filterMap fun md =>
    if md.parameset = name then some ⟨c.bins, md.paramSpec s.nominal⟩ else none

/-- The initial parameter point: the initial value the first modifier on a parameter set
asks for. An unknown name reads as 1. -/
def Model.init (m : Model K) : ParameterTable K :=
  ⟨fun name _ => ((m.paramSpecs name).head?.map (·.2.init)).getD 1⟩

/-- The bounds the first modifier on a parameter set asks for, if the set exists. -/
def Model.bounds (m : Model K) (name : String) : Option (K × K) :=
  (m.paramSpecs name).head?.map (·.2.bounds)

/-! ## 4. Well-formedness -/

/-- The `(channel, sample)` pairs that have a modifier on the parameter `name`. -/
def Model.carriers (m : Model K) (name : String) : List (String × String) :=
  m.channels.flatMap fun c => c.samples.filterMap fun s =>
    if s.modifiers.any (·.parameset = name) then some (c.name, s.name) else none

/-- The parameter `p` is used only where its sharing rule allows. -/
def Sharing.Allows (m : Model K) (p : String) : Sharing → Prop
  | .anywhere => True
  | .oneChannel => ∀ x ∈ m.carriers p, ∀ y ∈ m.carriers p, x.1 = y.1
  | .oneSample => (m.carriers p).length ≤ 1

instance (m : Model K) (p : String) (s : Sharing) : Decidable (s.Allows m p) := by
  cases s <;> unfold Sharing.Allows <;> infer_instance

/-- Channel names are distinct, modifiers that share a name agree on the parameter set,
and every parameter is used only where it may be. -/
def Model.WellFormed (m : Model K) : Prop :=
  (m.channels.map (·.name)).Nodup ∧
    ∀ c ∈ m.channels, ∀ s ∈ c.samples, ∀ md ∈ s.modifiers,
      md.paramSet s.nominal ∈ m.paramSets ∧ (md.paramSpec s.nominal).sharing.Allows m md.parameset

instance (m : Model K) : Decidable m.WellFormed := by
  unfold Model.WellFormed
  infer_instance

/-- The rows name exactly the parameter sets of the model, with the right sizes. -/
def Model.Accepts (m : Model K) (rows : List (String × List K)) : Prop :=
  (∀ ps ∈ m.paramSets, (rows.lookup ps.name).map List.length = some ps.size) ∧
    ∀ row ∈ rows, row.1 ∈ m.paramSets.map (·.name)

instance (m : Model K) (rows : List (String × List K)) : Decidable (m.Accepts rows) := by
  unfold Model.Accepts
  infer_instance

/-! ## 5. The likelihood -/

def Constraint.pdf (a : ConstraintData K) (θ : ParameterTable K) : Constraint K → K
  | .gaus p i _ σ => normal (a.values p i) (θ.values p i) σ
  | .pois p i τ => poisson (a.values p i) (τ * θ.values p i)

def Constraint.logpdf (a : ConstraintData K) (θ : ParameterTable K) : Constraint K → K
  | .gaus p i _ σ => logNormal (a.values p i) (θ.values p i) σ
  | .pois p i τ => logPoisson (a.values p i) (τ * θ.values p i)

/-- A Poisson term for every bin of every channel, times the constraint terms. -/
def Model.pdf (m : Model K) (d : Data K) (θ : ParameterTable K) : K :=
  (m.channels.map fun c =>
      (List.ofFn fun b : Fin c.bins =>
        poisson (d.counts.values c.name b) (c.rate θ b)).prod).prod
    * (m.constraints.map (·.pdf d.aux θ)).prod

/-- The logarithm of `Model.pdf`, written as a sum. -/
def Model.logpdf (m : Model K) (d : Data K) (θ : ParameterTable K) : K :=
  (m.channels.map fun c =>
      (List.ofFn fun b : Fin c.bins =>
        logPoisson (d.counts.values c.name b) (c.rate θ b)).sum).sum
    + (m.constraints.map (·.logpdf d.aux θ)).sum

/-! ## 6. Admissibility -/

def Constraint.Admissible (θ : ParameterTable K) : Constraint K → Prop
  | .gaus _ _ _ σ => 0 < σ
  | .pois p i τ => 0 < τ * θ.values p i

/-- Every expected rate and every constraint term has a valid distribution at `θ`. -/
def Model.Admissible (m : Model K) (θ : ParameterTable K) : Prop :=
  (∀ c ∈ m.channels, ∀ b : Fin c.bins, 0 < c.rate θ b) ∧
    ∀ k ∈ m.constraints, k.Admissible θ

/-! ## 7. An interpolation code that no model can select -/

/-- Quadratic interpolation with linear extrapolation, in the continuous form that ROOT
implements. It is not an alternative of `AdditiveModifierInterp`. -/
def code2 (lo nom hi α : K) : K :=
  let a := (hi + lo) / 2 - nom
  let b := (hi - lo) / 2
  if α ≤ -1 then (lo - nom) + (b - 2 * a) * (α + 1)
  else if α < 1 then a * α ^ 2 + b * α
  else (hi - nom) + (b + 2 * a) * (α - 1)

end HistFactory
