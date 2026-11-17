import HistFactory.Trusted

namespace HistFactory

open Number
variable {K : Type} [Number K]


def code2 (lo nom hi α : K) : K :=
  let a := (hi + lo) / 2 - nom
  let b := (hi - lo) / 2
  if α ≤ -1 then (lo - nom) + (b - 2 * a) * (α + 1)
  else if α < 1 then a * α ^ 2 + b * α
  else (hi - nom) + (b + 2 * a) * (α - 1)


inductive NormInterp
  | code1
  | code4
  deriving DecidableEq, Repr

inductive HistoInterp
  | code0
  | code2
  | code4p
  deriving DecidableEq, Repr

def NormInterp.eval : NormInterp → K → K → K → K
  | .code1 => HistFactory.code1
  | .code4 => HistFactory.code4

def HistoInterp.eval : HistoInterp → K → K → K → K → K
  | .code0 => HistFactory.code0
  | .code2 => HistFactory.code2
  | .code4p => HistFactory.code4p

inductive Modifier (K : Type) (n : Nat)
  | normfactor (name : String)
  | shapefactor (name : String)
  | lumi (name : String) (nominal sigma : K)
  | normsys (name : String) (lo hi : K)
  | histosys (name : String) (lo hi : Fin n → K)
  | shapesys (name : String) (unc : Fin n → K)
  | staterror (name : String) (unc : Fin n → K)

structure Sample (K : Type) (n : Nat) where
  name : String
  data : Fin n → K
  modifiers : List (Modifier K n)

structure Channel (K : Type) where
  name : String
  bins : Nat
  samples : List (Sample K bins)

structure Model (K : Type) where
  channels : List (Channel K)
  normsys : NormInterp := .code4
  histosys : HistoInterp := .code4p

abbrev Table (K : Type) := String → Nat → K

def Table.ofList (rows : List (String × List K)) : Table K :=
  fun name i => ((rows.lookup name).getD []).getD i 0

structure Data (K : Type) where
  counts : Table K
  aux : Table K

def Modifier.name : Modifier K n → String
  | .normfactor p => p
  | .shapefactor p => p
  | .lumi p _ _ => p
  | .normsys p _ _ => p
  | .histosys p _ _ => p
  | .shapesys p _ => p
  | .staterror p _ => p

def Modifier.factor (I : NormInterp) (θ : Table K) (b : Fin n) : Modifier K n → K
  | .normfactor p => θ p 0
  | .shapefactor p => θ p b
  | .lumi p _ _ => θ p 0
  | .normsys p lo hi => I.eval lo hi (θ p 0)
  | .histosys _ _ _ => 1
  | .shapesys p _ => θ p b
  | .staterror p _ => θ p b

def Modifier.shift (I : HistoInterp) (θ : Table K) (nom : Fin n → K) (b : Fin n) :
    Modifier K n → K
  | .histosys p lo hi => I.eval (lo b) (nom b) (hi b) (θ p 0)
  | _ => 0

def Sample.rate (s : Sample K n) (N : NormInterp) (H : HistoInterp) (θ : Table K)
    (b : Fin n) : K :=
  (s.data b + (s.modifiers.map (·.shift H θ s.data b)).sum)
    * (s.modifiers.map (·.factor N θ b)).prod

def Channel.rate (c : Channel K) (N : NormInterp) (H : HistoInterp) (θ : Table K)
    (b : Fin c.bins) : K :=
  (c.samples.map (·.rate N H θ b)).sum

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
    | .staterror p unc => if p = name then some (s.data b, unc b) else none
    | _ => none

def Channel.mcWidth (c : Channel K) (name : String) (b : Fin c.bins) : K :=
  sqrt ((c.mcStat name b).map (·.2 ^ 2)).sum / ((c.mcStat name b).map (·.1)).sum

def Modifier.constraints (c : Channel K) (s : Sample K c.bins) :
    Modifier K c.bins → List (Constraint K)
  | .normfactor _ => []
  | .shapefactor _ => []
  | .lumi p nominal sigma => [.gaus p 0 nominal sigma]
  | .normsys p _ _ => [.gaus p 0 0 1]
  | .histosys p _ _ => [.gaus p 0 0 1]
  | .shapesys p unc => List.ofFn fun b : Fin c.bins => .pois p b ((s.data b / unc b) ^ 2)
  | .staterror p _ => List.ofFn fun b : Fin c.bins => .gaus p b 1 (c.mcWidth p b)

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

def Modifier.paramSet : Modifier K n → ParamSet
  | .normfactor p => ⟨p, 1, .free⟩
  | .shapefactor p => ⟨p, n, .free⟩
  | .lumi p _ _ => ⟨p, 1, .normal⟩
  | .normsys p _ _ => ⟨p, 1, .normal⟩
  | .histosys p _ _ => ⟨p, 1, .normal⟩
  | .shapesys p _ => ⟨p, n, .poisson⟩
  | .staterror p _ => ⟨p, n, .normal⟩

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
    if s.modifiers.any (·.name = name) then some (c.name, s.name) else none

def Modifier.Local (m : Model K) : Modifier K n → Prop
  | .shapesys p _ => (m.carriers p).length ≤ 1
  | .staterror p _ => ∀ x ∈ m.carriers p, ∀ y ∈ m.carriers p, x.1 = y.1
  | _ => True

instance (m : Model K) (md : Modifier K n) : Decidable (md.Local m) := by
  cases md <;> unfold Modifier.Local <;> infer_instance

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
        poisson (d.counts c.name b) (c.rate m.normsys m.histosys θ b)).prod).prod
    * (m.constraints.map (·.pdf d.aux θ)).prod

def Model.logpdf (m : Model K) (d : Data K) (θ : Table K) : K :=
  (m.channels.map fun c =>
      (List.ofFn fun b : Fin c.bins =>
        logPoisson (d.counts c.name b) (c.rate m.normsys m.histosys θ b)).sum).sum
    + (m.constraints.map (·.logpdf d.aux θ)).sum

def Constraint.Admissible (θ : Table K) : Constraint K → Prop
  | .gaus _ _ _ σ => 0 < σ
  | .pois p i τ => 0 < τ * θ p i

def Model.Admissible (m : Model K) (θ : Table K) : Prop :=
  (∀ c ∈ m.channels, ∀ b : Fin c.bins, 0 < c.rate m.normsys m.histosys θ b) ∧
    ∀ k ∈ m.constraints, k.Admissible θ

end HistFactory
