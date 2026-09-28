import Mathlib
import Definitions.FLT.Def_ModularCurve_ModuliPoint
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_Point_vcInvFun_neg_heq_neg

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_Point_vcInvFun_neg_heq_neg.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_Point_vcInvFun_neg_heq_neg.WeierstrassCurve.Affine"

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY a₃ a₁ variableChange_a₃ variableChange_a₆ variableChange_a₂ toAffine Affine.Point variableChange_a₁ variableChange_a₄ VariableChange Affine.Point.neg_some"
namespace Affine
p2m_export "WeierstrassCurve.Affine" "negY Point Point.neg_some vcXInv vcYInv Point.vcInvFun"
namespace Point
p2m_export "WeierstrassCurve.Affine.Point" "some zero neg_some vcInvFun"
p2m_open "WeierstrassCurve.Affine.Point WeierstrassCurve.Affine WeierstrassCurve"

variable {F : Type*} [Field F]

theorem negVariableChange_smul' (W : WeierstrassCurve F) :
    (⟨-1, 0, -W.a₁, -W.a₃⟩ : VariableChange F) • W = W := by
  ext
  · simp only [variableChange_a₁, inv_neg, inv_one, Units.val_neg, Units.val_one]; ring
  · simp only [variableChange_a₂, inv_neg, inv_one, Units.val_neg, Units.val_one]; ring
  · simp only [variableChange_a₃, inv_neg, inv_one, Units.val_neg, Units.val_one]; ring
  · simp only [variableChange_a₄, inv_neg, inv_one, Units.val_neg, Units.val_one]; ring
  · simp only [variableChange_a₆, inv_neg, inv_one, Units.val_neg, Units.val_one]; ring

end WeierstrassCurve.Affine.Point

p2m_open "WeierstrassCurve P2MW.S_WeierstrassCurve_Affine_Point_vcInvFun_neg_heq_neg.WeierstrassCurve WeierstrassCurve.Affine P2MW.S_WeierstrassCurve_Affine_Point_vcInvFun_neg_heq_neg.WeierstrassCurve.Affine WeierstrassCurve.Affine.Point P2MW.S_WeierstrassCurve_Affine_Point_vcInvFun_neg_heq_neg.WeierstrassCurve.Affine.Point"

theorem solution {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) (P : W.toAffine.Point) :
    HEq (vcInvFun (⟨-1, 0, -W.a₁, -W.a₃⟩ : VariableChange F) W.toAffine P) (-P) := by
  have hW : ((⟨-1, 0, -W.a₁, -W.a₃⟩ : VariableChange F) • W).toAffine = W.toAffine := negVariableChange_smul' W
  cases P with
  | zero => exact ModularCurve.Point.heq_zero hW
  | some x y h =>
    rw [Affine.Point.neg_some]
    simp only [vcInvFun]
    refine ModularCurve.Point.heq_some hW ?_ ?_
    · simp [vcXInv]
    · simp only [vcYInv, Affine.negY, inv_neg, inv_one, Units.val_neg, Units.val_one, sub_zero]
      ring

end S_WeierstrassCurve_Affine_Point_vcInvFun_neg_heq_neg
end P2MW
export P2MW.S_WeierstrassCurve_Affine_Point_vcInvFun_neg_heq_neg (solution)
