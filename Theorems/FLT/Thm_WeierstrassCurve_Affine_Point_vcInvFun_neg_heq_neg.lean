import Mathlib
import Definitions.FLT.Def_ModularCurve_ModuliPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine
theorem WeierstrassCurve.Affine.Point.vcInvFun_neg_heq_neg {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) (P : W.toAffine.Point) :
    HEq (Point.vcInvFun (⟨-1, 0, -W.a₁, -W.a₃⟩ : VariableChange F) W.toAffine P) (-P) := by sorry
