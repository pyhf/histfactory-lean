-- LH: implement HiFa.Number with Float to allow for real evaluation

import HistFactory.Trusted


namespace HistFactory

-- LH: Lanczos approximation for Gamma function
def Float.logGamma (x : Float) : Float :=
  let c : Array Float := #[
      0.99999999999980993,
      676.5203681218851,
      -1259.1392167224028,
      771.32342877765313,
      -176.61502916214059,
      12.507343278686905,
      -0.13857109526572012,
      9.9843695780195716e-6,
      1.5056327351493116e-7
  ]
  let y := x - 1
  let a := (List.range 8).foldl
    (fun acc i => acc + c.getD (i + 1) 0 / (y + Float.ofNat (i + 1))) (c.getD 0 0)
  let t := y + 7.5
  0.5 * Float.log (2 * 3.141592653589793) + (y + 0.5) * Float.log t - t + Float.log a

instance : NatCast Float := ⟨Float.ofNat⟩
instance : Zero Float := ⟨0.0⟩
instance : One Float := ⟨1.0⟩

instance : Number Float where
  npow x n := Float.pow x (Float.ofNat n)
  rpow := Float.pow
  decLT := inferInstance
  decLE := inferInstance
  exp := Float.exp
  log := Float.log
  sqrt := Float.sqrt
  gamma := fun x => Float.exp (Float.logGamma x)
  logGamma := Float.logGamma
  pi := 3.141592653589793

end HistFactory
