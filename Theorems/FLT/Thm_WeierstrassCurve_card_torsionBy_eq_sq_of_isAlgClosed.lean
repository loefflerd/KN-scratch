import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
theorem WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
    (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hn : (n : F) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ W.toAffine.Point n) = n ^ 2 := by sorry
