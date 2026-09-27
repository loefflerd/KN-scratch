import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped nonZeroDivisors
theorem WeierstrassCurve.Affine.CoordinateRing.natDegree_norm_eq_finsum_count {K : Type*} [Field K] [IsAlgClosed K] (W : WeierstrassCurve K) [IsDedekindDomain W.toAffine.CoordinateRing] {a : W.toAffine.CoordinateRing} (ha : a ≠ 0) : ((Algebra.norm (Polynomial K) a).natDegree : ℤ) = ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum W.toAffine.CoordinateRing, FractionalIdeal.count W.toAffine.FunctionField v (FractionalIdeal.spanSingleton W.toAffine.CoordinateRing⁰ (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField a)) := by sorry
