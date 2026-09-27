import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem WeierstrassCurve.Affine.FunctionField.exists_eq_valuationSubring_of_X_mem {K : Type*} [Field K] (W : WeierstrassCurve K) [IsDedekindDomain W.toAffine.CoordinateRing] (O : ValuationSubring W.toAffine.FunctionField) (hO : O ≠ ⊤) (hK : ∀ c : K, algebraMap K W.toAffine.FunctionField c ∈ O) (hX : algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X)) ∈ O) : ∃ v : IsDedekindDomain.HeightOneSpectrum W.toAffine.CoordinateRing, O = (v.valuation W.toAffine.FunctionField).valuationSubring := by sorry
