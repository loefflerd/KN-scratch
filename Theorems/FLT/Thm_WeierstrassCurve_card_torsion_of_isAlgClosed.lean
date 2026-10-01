import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.card_torsion_of_isAlgClosed {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K] [DecidableEq K] (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) : Nat.card (Submodule.torsionBy ℤ (W⁄K).Point n) = n ^ 2 := by sorry
