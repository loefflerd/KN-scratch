import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem WeierstrassCurve.Affine.Point.exists_zsmul_eq_of_isAlgClosed {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] (E : WeierstrassCurve K) [E.IsElliptic] {n : ℤ} (hn : n ≠ 0) (P : E.toAffine.Point) : ∃ Q : E.toAffine.Point, n • Q = P := by sorry
