import HistFactory.Trusted

namespace HistFactory

open Number
variable {K : Type} [Number K] {n : Nat}

def code2 (lo nom hi α : K) : K :=
  let a := (hi + lo) / 2 - nom
  let b := (hi - lo) / 2
  if α ≤ -1 then (lo - nom) + (b - 2 * a) * (α + 1)
  else if α < 1 then a * α ^ 2 + b * α
  else (hi - nom) + (b + 2 * a) * (α - 1)

abbrev Table (K : Type) := String → Nat → K

def Table.ofList (rows : List (String × List K)) : Table K :=
  fun name i => ((rows.lookup name).getD []).getD i 0

structure Data (K : Type) where
  counts : Table K
  aux : Table K

def Effect.factor (γ : Nat → K) (b : Fin n) : Effect K n → K
  | .normfactor => γ 0
  | .shapefactor => γ b
  | .lumi _ _ => γ 0
  | .normsys lo hi I => I.eval lo hi (γ 0)
  | .histosys _ _ _ => 1
  | .shapesys _ => γ b
  | .staterror _ => γ b

def Effect.shift (γ : Nat → K) (nom : Fin n → K) (b : Fin n) : Effect K n → K
  | .histosys lo hi I => I.eval (lo b) (nom b) (hi b) (γ 0)
  | _ => 0

def Modifier.factor (θ : Table K) (b : Fin n) (m : Modifier K n) : K :=
  m.effect.factor (θ m.parameset) b

def Modifier.shift (θ : Table K) (nom : Fin n → K) (b : Fin n) (m : Modifier K n) : K :=
  m.effect.shift (θ m.parameset) nom b

def Sample.rate (s : Sample K n) (θ : Table K) (b : Fin n) : K :=
  (s.nominal b + (s.modifiers.map (·.shift θ s.nominal b)).sum)
    * (s.modifiers.map (·.factor θ b)).prod

def Channel.rate (c : Channel K) (θ : Table K) (b : Fin c.bins) : K :=
  (c.samples.map (·.rate θ b)).sum

inductive Constraint (K : Type)
  | gaus (name : String) (index : Nat) (observed width : K)
  | pois (name : String) (index : Nat) (tau : K)

def Constraint.param : Constraint K → String × Nat
  | .gaus p i _ _ => (p, i)
  | .pois p i _ => (p, i)

def Constraint.observed : Constraint K → K
  | .gaus _ _ a _ => a
  | .pois _ _ τ => τ

def Constraint.pdf (a θ : Table K) : Constraint K → K
  | .gaus p i _ σ => normal (a p i) (θ p i) σ
  | .pois p i τ => poisson (a p i) (τ * θ p i)

def Constraint.logpdf (a θ : Table K) : Constraint K → K
  | .gaus p i _ σ => logNormal (a p i) (θ p i) σ
  | .pois p i τ => logPoisson (a p i) (τ * θ p i)

def Channel.mcStat (c : Channel K) (name : String) (b : Fin c.bins) : List (K × K) :=
  c.samples.flatMap fun s => s.modifiers.filterMap fun
    | ⟨p, .staterror unc⟩ => if p = name then some (s.nominal b, unc b) else none
    | _ => none

def Channel.mcWidth (c : Channel K) (name : String) (b : Fin c.bins) : K :=
  sqrt ((c.mcStat name b).map (·.2 ^ 2)).sum / ((c.mcStat name b).map (·.1)).sum

def Effect.constraints (c : Channel K) (s : Sample K c.bins) (p : String) :
    Effect K c.bins → List (Constraint K)
  | .normfactor => []
  | .shapefactor => []
  | .lumi nominal sigma => [.gaus p 0 nominal sigma]
  | .normsys _ _ _ => [.gaus p 0 0 1]
  | .histosys _ _ _ => [.gaus p 0 0 1]
  | .shapesys unc => List.ofFn fun b : Fin c.bins => .pois p b ((s.nominal b / unc b) ^ 2)
  | .staterror _ => List.ofFn fun b : Fin c.bins => .gaus p b 1 (c.mcWidth p b)

def Modifier.constraints (c : Channel K) (s : Sample K c.bins) (m : Modifier K c.bins) :
    List (Constraint K) :=
  m.effect.constraints c s m.parameset

def firstBy {α κ : Type} [DecidableEq κ] (key : α → κ) : List α → List α
  | [] => []
  | a :: rest => a :: (firstBy key rest).filter (key · ≠ key a)

def Model.constraints (m : Model K) : List (Constraint K) :=
  firstBy Constraint.param <|
    m.channels.flatMap fun c => c.samples.flatMap fun s =>
      s.modifiers.flatMap (·.constraints c s)

inductive Kind
  | free
  | normal
  | poisson
  deriving DecidableEq, Repr

structure ParamSet where
  name : String
  size : Nat
  kind : Kind
  deriving DecidableEq, Repr

def Effect.size : Effect K n → Nat
  | .normfactor => 1
  | .shapefactor => n
  | .lumi _ _ => 1
  | .normsys _ _ _ => 1
  | .histosys _ _ _ => 1
  | .shapesys _ => n
  | .staterror _ => n

def Effect.kind : Effect K n → Kind
  | .normfactor => .free
  | .shapefactor => .free
  | .lumi _ _ => .normal
  | .normsys _ _ _ => .normal
  | .histosys _ _ _ => .normal
  | .shapesys _ => .poisson
  | .staterror _ => .normal

def Modifier.paramSet (m : Modifier K n) : ParamSet :=
  ⟨m.parameset, m.effect.size, m.effect.kind⟩

def Model.paramSets (m : Model K) : List ParamSet :=
  firstBy ParamSet.name <|
    m.channels.flatMap fun c => c.samples.flatMap fun s => s.modifiers.map (·.paramSet)

def Model.size (m : Model K) : Nat :=
  (m.paramSets.map (·.size)).sum

def Model.init (m : Model K) : Table K :=
  fun name i =>
    match m.constraints.find? (·.param = (name, i)) with
    | some (.gaus _ _ a _) => a
    | _ => 1

def Model.auxdata (m : Model K) : Table K :=
  fun name i =>
    match m.constraints.find? (·.param = (name, i)) with
    | some k => k.observed
    | none => 0

def Model.observed (m : Model K) (counts : List (String × List K)) : Data K :=
  ⟨Table.ofList counts, m.auxdata⟩

def Model.carriers (m : Model K) (name : String) : List (String × String) :=
  m.channels.flatMap fun c => c.samples.filterMap fun s =>
    if s.modifiers.any (·.parameset = name) then some (c.name, s.name) else none

def Effect.Local (m : Model K) (p : String) : Effect K n → Prop
  | .shapesys _ => (m.carriers p).length ≤ 1
  | .staterror _ => ∀ x ∈ m.carriers p, ∀ y ∈ m.carriers p, x.1 = y.1
  | _ => True

instance (m : Model K) (p : String) (e : Effect K n) : Decidable (e.Local m p) := by
  cases e <;> unfold Effect.Local <;> infer_instance

def Modifier.Local (m : Model K) (md : Modifier K n) : Prop :=
  md.effect.Local m md.parameset

instance (m : Model K) (md : Modifier K n) : Decidable (md.Local m) := by
  unfold Modifier.Local
  infer_instance

def Model.WellFormed (m : Model K) : Prop :=
  (m.channels.map (·.name)).Nodup ∧
    ∀ c ∈ m.channels, ∀ s ∈ c.samples, ∀ md ∈ s.modifiers,
      md.paramSet ∈ m.paramSets ∧ md.Local m

instance (m : Model K) : Decidable m.WellFormed := by
  unfold Model.WellFormed
  infer_instance

def Model.Accepts (m : Model K) (rows : List (String × List K)) : Prop :=
  (∀ ps ∈ m.paramSets, (rows.lookup ps.name).map List.length = some ps.size) ∧
    ∀ row ∈ rows, row.1 ∈ m.paramSets.map (·.name)

instance (m : Model K) (rows : List (String × List K)) : Decidable (m.Accepts rows) := by
  unfold Model.Accepts
  infer_instance

def Model.pdf (m : Model K) (d : Data K) (θ : Table K) : K :=
  (m.channels.map fun c =>
      (List.ofFn fun b : Fin c.bins =>
        poisson (d.counts c.name b) (c.rate θ b)).prod).prod
    * (m.constraints.map (·.pdf d.aux θ)).prod

def Model.logpdf (m : Model K) (d : Data K) (θ : Table K) : K :=
  (m.channels.map fun c =>
      (List.ofFn fun b : Fin c.bins =>
        logPoisson (d.counts c.name b) (c.rate θ b)).sum).sum
    + (m.constraints.map (·.logpdf d.aux θ)).sum

def Constraint.Admissible (θ : Table K) : Constraint K → Prop
  | .gaus _ _ _ σ => 0 < σ
  | .pois p i τ => 0 < τ * θ p i

def Model.Admissible (m : Model K) (θ : Table K) : Prop :=
  (∀ c ∈ m.channels, ∀ b : Fin c.bins, 0 < c.rate θ b) ∧
    ∀ k ∈ m.constraints, k.Admissible θ

end HistFactory
