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


/-

LH: A Sample type parametrized by scalar type and size n

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


end HistFactory
