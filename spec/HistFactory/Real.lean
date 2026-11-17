-- LH: implement HiFa.Number with Real to allow for proofs
-- LH: only this requires Mathlib (not needed for Float impl)

import HistFactory.Trusted
import Mathlib

namespace HistFactory

noncomputable instance : Number ℝ where
  npow x n := x ^ n
  rpow x y := x ^ y
  decLT := inferInstance
  decLE := inferInstance
  exp := Real.exp
  log := Real.log
  sqrt := Real.sqrt
  gamma := Real.Gamma
  logGamma := fun x => Real.log (Real.Gamma x)
  pi := Real.pi

open Real

-- LH: prove (trivially) that the Number ops (on Real instantiation) are the Mathlib ops
@[simp] theorem exp_real (x : ℝ) : Number.exp x = exp x := rfl
@[simp] theorem log_real (x : ℝ) : Number.log x = log x := rfl
@[simp] theorem sqrt_real (x : ℝ) : Number.sqrt x = √x := rfl
@[simp] theorem gamma_real (x : ℝ) : Number.gamma x = Gamma x := rfl
@[simp] theorem logGamma_real (x : ℝ) : Number.logGamma x = log (Gamma x) := rfl
@[simp] theorem pi_real : (Number.pi : ℝ) = π := rfl

theorem poisson_real (k ν : ℝ) : poisson k ν = ν ^ k * exp (-ν) / Gamma (k + 1) := rfl

theorem normal_real (x μ σ : ℝ) :
    normal x μ σ = exp (-(x - μ) ^ 2 / (2 * σ ^ 2)) / (σ * √(2 * π)) := rfl

theorem logPoisson_real (k ν : ℝ) :
    logPoisson k ν = k * log ν - ν - log (Gamma (k + 1)) := rfl

theorem logNormal_real (x μ σ : ℝ) :
    logNormal x μ σ = -(x - μ) ^ 2 / (2 * σ ^ 2) - log (σ * √(2 * π)) := rfl

end HistFactory
