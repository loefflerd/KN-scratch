import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem WeierstrassCurve.Affine.FunctionField.exists_valuation_eq_exp_natDegree_norm {K : Type*} [Field K] (W : WeierstrassCurve K) : ∃ v : Valuation W.toAffine.FunctionField (WithZero (Multiplicative ℤ)), ∀ f : W.toAffine.CoordinateRing, f ≠ 0 → v (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField f) = WithZero.exp ((Algebra.norm (Polynomial K) f).natDegree : ℤ) := by sorry
