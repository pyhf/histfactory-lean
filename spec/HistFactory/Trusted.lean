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




end HistFactory
