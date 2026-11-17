import HistFactory.Trusted
import HistFactory.Real
import HistFactory.Float

open Mathlib
open Real
open Nat
open HistFactory

-- LH: example proof
theorem logPoisson_natCast (k : ℕ) (ν : ℝ) :
    logPoisson (k : ℝ) ν = k * log ν - ν - log (k ! : ℝ) := by
  rw [logPoisson_real, Gamma_nat_eq_factorial]

-- LH: example proof that at α = 1 code0 is hi-nom
theorem code0(lo nom hi : ℝ) :
  (code0 lo nom hi 1) = hi - nom := by
  unfold HistFactory.code0
  split_ifs with h
  · norm_num at h
  · ring
