import Mathlib
import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem WeierstrassCurve.Affine.exists_infinitePlace_deg_eq_one {F : Type*} [Field F] (W : WeierstrassCurve.Affine F) : ∃ vInf : AlgebraicCurve.Place F W.FunctionField, vInf.deg = 1 ∧ (¬ ∀ r : W.CoordinateRing, algebraMap W.CoordinateRing W.FunctionField r ∈ vInf.toValuationSubring) ∧ ∀ v : AlgebraicCurve.Place F W.FunctionField, (¬ ∀ r : W.CoordinateRing, algebraMap W.CoordinateRing W.FunctionField r ∈ v.toValuationSubring) → v = vInf := by sorry
