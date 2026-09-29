import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem WeierstrassCurve.finite_torsionBy_of_natCast_ne_zero (k : Type*) [Field k] [DecidableEq k] (W : WeierstrassCurve k) [W.IsElliptic]
    (n : ℕ) (hn : (n : k) ≠ 0) :
    Finite (Submodule.torsionBy ℤ W.toAffine.Point n) := by sorry
