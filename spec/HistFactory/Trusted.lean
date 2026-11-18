namespace HistFactory

-- declare a generic number class as a basic scalar for HistFactory
-- concretely for proofs with might then be a true real, i.e. K=ℝ, while for
-- explicit calculations we would use `K = Float'

class Number (K : Type) extends Add K, Sub K, Mul K, Div K, Neg K, Zero K, One K, NatCast K,
    OfScientific K, LT K, LE K where
  npow : K → Nat → K
  rpow : K → K → K
  decLT : DecidableLT K
  decLE : DecidableLE K
  exp : K → K
  log : K → K
  sqrt : K → K
  gamma : K → K
  logGamma : K → K
  pi : K

-- LH: make number operations directly accessible by member name
open Number

-- LH: add implicit and and instance parameters to all defs automatically
variable {K : Type} [Number K] {n : Nat}

-- LH: a simple table type for string-indexed vectors (think: table["name"][index])
abbrev Table (K : Type) := String → Nat → K

-- LH: make symbols ^, <, <= refer to Number's methods npow, rpow, <, <=
scoped instance (priority := low) {k : Nat} : OfNat K k := ⟨Nat.cast (OfNat.ofNat k)⟩
scoped instance : HPow K Nat K := ⟨npow⟩
scoped instance : HPow K K K := ⟨rpow⟩
scoped instance : DecidableLT K := decLT
scoped instance : DecidableLE K := decLE

-- LH: add basic prob and logprob functions
-- Gamma is used to allow non-integer k TOPROOF(!)
def poisson (k ν : K) : K :=
  ν ^ k * exp (-ν) / gamma (k + 1)

def normal (x μ σ : K) : K :=
  exp (-(x - μ) ^ 2 / (2 * σ ^ 2)) / (σ * sqrt (2 * pi))

def logPoisson (k ν : K) : K :=
  k * log ν - ν - logGamma (k + 1)

def logNormal (x μ σ : K) : K :=
  -(x - μ) ^ 2 / (2 * σ ^ 2) - log (σ * sqrt (2 * pi))

-- LH: Interpolation Codes

def code0 (lo nom hi α : K) : K :=
  if α ≤ 0 then α * (nom - lo) else α * (hi - nom)

def code1 (lo hi α : K) : K :=
  if α ≤ 0 then lo ^ (-α) else hi ^ α

def code4p (lo nom hi α : K) : K :=
  let S := ((hi - nom) + (nom - lo)) / 2
  let A := ((hi - nom) - (nom - lo)) / 16
  if α ≤ -1 then α * (nom - lo)
  else if α < 1 then S * α + A * (15 * α ^ 2 - 10 * α ^ 4 + 3 * α ^ 6)
  else α * (hi - nom)

def code4Poly (lo hi α : K) : K :=
  let S₀ := (hi + lo) / 2
  let A₀ := (hi - lo) / 2
  let S₁ := (hi * log hi - lo * log lo) / 2
  let A₁ := (hi * log hi + lo * log lo) / 2
  let S₂ := (hi * (log hi) ^ 2 + lo * (log lo) ^ 2) / 2
  let A₂ := (hi * (log hi) ^ 2 - lo * (log lo) ^ 2) / 2
  1 + (15 * A₀ - 7 * S₁ + A₂) / 8 * α
    + (-24 + 24 * S₀ - 9 * A₁ + S₂) / 8 * α ^ 2
    + (-5 * A₀ + 5 * S₁ - A₂) / 4 * α ^ 3
    + (12 - 12 * S₀ + 7 * A₁ - S₂) / 4 * α ^ 4
    + (3 * A₀ - 3 * S₁ + A₂) / 8 * α ^ 5
    + (-8 + 8 * S₀ - 5 * A₁ + S₂) / 8 * α ^ 6

def code4 (lo hi α : K) : K :=
  if α ≤ -1 then lo ^ (-α) else if α < 1 then code4Poly lo hi α else hi ^ α



/-
LH: there are two types of interpolation methods

1) interpolators that are used for "multiplicative" modifiers (MultiplicativeInterp)
2) interpolators that are used for "addtivive" modifiers (AdditiveModifierInterp)

we define two sum types (types, where a value is one of the given options) to reflect this

-/

-- LH: the sum types
inductive MultiplicativeInterp
  | code1
  | code4

inductive AdditiveModifierInterp
  | code0
  | code4p

/-
LH: a dispatch function based on the value of the sum type to the interpolation function
-/
def MultiplicativeInterp.eval : MultiplicativeInterp → K → K → K → K
  | .code1 => HistFactory.code1
  | .code4 => HistFactory.code4

def AdditiveModifierInterp.eval : AdditiveModifierInterp → K → K → K → K → K
  | .code0 => HistFactory.code0
  | .code4p => HistFactory.code4p



/-
1. LH: The parameter model for HistFactory
========================================

* There are two types of parameter sets (scalars and vectors) -> shape
* Parameters have nominal parameers values (init) and a range (bounds)
* some parameters come with a constraint term
* whether the parameter set may be bound to multiple effects (sharing)

-/

structure ParameterTable (K : Type) where
  values : Table K


inductive Shape
  | scalar
  | perBin

def Shape.size (s : Shape) (n : Nat) : Nat :=
  match s with
  | .scalar => 1
  | .perBin => n

def Shape.index (s : Shape) (b : Fin n) : Nat :=
  match s with
  | .scalar => 0
  | .perBin => b

/-
LH: the three options of how a parameter can be shared

* for ordinary systematics any sample in any channel can bind a modifier to it
* for shapesys the situation is more complicated since the constraint term / width
  depends on the data passed in the sample, so it cannot be shared / it's unique per sample (oneSample)
* for staterror, multiple samples of the same can participate in it (they'll jointly get varied according to barlow beaston)

-/

inductive Sharing
  | anywhere
  | oneChannel
  | oneSample

/-
LH: the constraint model with a few options

The mcStat and Poisson consstraints are "vector constraints"
where the constraint parameters are passed as lookup functions
indexed by the channel size n

-/

inductive ConstraintSpec (K : Type) (n : Nat)
  | free
  | normal (aux sigma : K)
  | mcStat (unc : Fin n → K)
  | poisson (tau : Fin n → K)


structure ParamSpec (K : Type) (n : Nat) where
  shape : Shape
  sharing : Sharing
  init : K
  bounds : K × K
  constraint : ConstraintSpec K n


/-
2. LH: The modifier model of HistFactory
========================================


the implemenattion of the known effects

each fully defines
* required parameter set
* its concrete modification to the bin

-/

inductive Modification (K : Type)
  | times (factor : K)
  | plus (shift : K)


/-
LH: the bin modification effect type is parametrized by both the scalar type and
a size n. There are seven known modifications

Some modifiers
* take vector-like data (histosys/shapesys/staterror)
* take only scalar data (normsys / lumi)
* take no data at all (normfactor, shapefactor)

-/

inductive Effect (K : Type) (n : Nat)
  | normfactor
  | shapefactor
  | lumi (nominal sigma : K)
  | normsys (lo hi : K) (interp : MultiplicativeInterp := .code4)
  | histosys (lo hi : Fin n → K) (interp : AdditiveModifierInterp := .code4p)
  | shapesys (unc : Fin n → K)
  | staterror (unc : Fin n → K)

/-

LH: A Modifier type parametrized by scalar type and size n
It is a pair of a string name and an effect
* the string name refers to parameter set that controls the effect
* the effect is on of the modification functions above

-/

structure Modifier (K : Type) (n : Nat) where
  parameset : String
  effect : Effect K n


structure EffectSpec (K : Type) (n : Nat) where
  paramspec : ParamSpec K n
  modification : (b : Fin n) → (x : K) → Modification K

def Effect.spec (nom : Fin n → K) : Effect K n → EffectSpec K n
  | .normfactor =>
    { paramspec :=⟨.scalar, .anywhere, 1, (0, 10), .free⟩
      modification := fun _ θ => .times θ }
  | .shapefactor =>
    { paramspec :=⟨.perBin, .anywhere, 1, (0, 10), .free⟩
      modification := fun _ θ_b => .times θ_b }
  | .lumi nominal sigma =>
    { paramspec :=⟨.scalar, .anywhere, nominal, (0, 10 * nominal), .normal nominal sigma⟩
      modification := fun _ θ => .times θ }
  | .normsys lo hi I =>
    { paramspec :=⟨.scalar, .anywhere, 0, (-5, 5), .normal 0 1⟩
      modification := fun _ θ => .times (I.eval lo hi θ) }
  | .histosys lo hi I =>
    { paramspec :=⟨.scalar, .anywhere, 0, (-5, 5), .normal 0 1⟩
      modification := fun b θ => .plus (I.eval (lo b) (nom b) (hi b) θ) }
  | .shapesys unc =>
    { paramspec :=⟨.perBin, .oneSample, 1, (1e-10, 10), .poisson fun b => (nom b / unc b) ^ 2⟩
      modification := fun _ θ_b => .times θ_b }
  | .staterror unc =>
    { paramspec :=⟨.perBin, .oneChannel, 1, (1e-10, 10), .mcStat unc⟩
      modification := fun _ θ_b => .times θ_b }


/-
LH:

* for each modifier we can produce a concrete modification given the bin and parameter value

* to compute the full rate for a sample we collect all shift modifications and all factor modifications
  and first apply the shifts and then factors

* the overall rate of a channel at some bin is the sum of the sample rates

-/

def Modifier.modification (θ : ParameterTable K) (nom : Fin n → K) (b : Fin n)
    (m : Modifier K n) : Modification K :=
  let spec := m.effect.spec nom
  let paramvalue := θ.values m.parameset (spec.paramspec.shape.index b)
  spec.modification b paramvalue


/-

3. LH: The overall main likelihood model of Histfactory
========================================


A Sample type parametrized by scalar type and size n
-/

structure Sample (K : Type) (n : Nat) where
  name : String
  nominal : Fin n → K
  modifiers : List (Modifier K n)


/-

LH: The Channel and Model types

Note that deliberately Channel is not parametetrized
by the size.. since a overall model is a list of
potentially differently sized channels

-/

structure Channel (K : Type) where
  name : String
  bins : Nat
  samples : List (Sample K bins)


structure Model (K : Type) where
  channels : List (Channel K)


def Sample.rate (s : Sample K n) (θ : ParameterTable K) (b : Fin n) : K :=
  let modifications := s.modifiers.map (·.modification θ s.nominal b)
  let shifts := modifications.filterMap fun | .plus x => some x | .times _ => none
  let factors := modifications.filterMap fun | .times x => some x | .plus _ => none
  (s.nominal b + shifts.sum) * factors.prod

def Channel.rate (c : Channel K) (θ : ParameterTable K) (b : Fin c.bins) : K :=
  (c.samples.map (·.rate θ b)).sum


end HistFactory
