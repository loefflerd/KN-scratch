import Definitions.FLT.Def_ModularCurve_CycSubRootBridgeN
import Definitions.FLT.Def_Isogeny_ConditionalCurrency
import Definitions.FLT.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Definitions.FLT.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.FLT.Def_ModularCurve_X0
import Theorems.FLT.Thm_WeierstrassCurve_Affine_eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward
import Theorems.FLT.Thm_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_abelTheorem
import Theorems.FLT.Thm_WeierstrassCurve_exists_functionFieldHom_fullKernelQuotient_pointMapOfPushforward_ker_eq_zmultiples
import Theorems.FLT.Thm_WeierstrassCurve_Affine_hasPrincipalDivisors_of_isAlgClosed
import Theorems.FLT.Thm_AlgebraicCurve_normFormulaAlong
import Theorems.FLT.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.FLT.Thm_ModularCurve_TatePoint_fullKernelIsRootAt_of_odd
import Theorems.FLT.Thm_ModularCurve_TatePoint_fullKernelDiscAt_of_odd
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_TatePoint_fullKernelIsRootAt
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap2_zero"

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "TatePoint.FullKernelIsRootAt"
namespace TatePoint
p2m_export "ModularCurve.TatePoint" "FullKernelIsRootAt FullKernelDiscAt isAlgClosed_H charZero_H H fullKernelIsRootAt_of_odd fullKernelDiscAt_of_odd"
p2m_open "ModularCurve.TatePoint ModularCurve"

attribute [local instance] isAlgClosed_H charZero_H

local notation "H" => HahnSeries ℚ (AlgebraicClosure ℚ)

theorem fullKernelIsRootAt_of_tower
    (N : ℕ) [NeZero N] : FullKernelIsRootAt N := by
  rcases Nat.even_or_odd N with hE | hO
  · intro _ W _ Q hQ hΔ data
    let : (W.fullKernelQuotient Q N).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    obtain ⟨gW, hgWc, hgWa⟩ :=
      WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_abelTheorem W.toAffine
    let := gW
    have : GenusOnePlaceGate.IsCentred W.toAffine := hgWc
    have : AbelTheorem W.toAffine := hgWa
    obtain ⟨gV, hgVc, hgVa⟩ :=
      WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_abelTheorem
        (W.fullKernelQuotient Q N).toAffine
    let := gV
    have : GenusOnePlaceGate.IsCentred (W.fullKernelQuotient Q N).toAffine := hgVc
    have : AbelTheorem (W.fullKernelQuotient Q N).toAffine := hgVa
    obtain ⟨ι, hι, hfin, hker⟩ :=
      WeierstrassCurve.exists_functionFieldHom_fullKernelQuotient_pointMapOfPushforward_ker_eq_zmultiples
        hQ hΔ
    have : HasPrincipalDivisors H W.toAffine.FunctionField :=
      WeierstrassCurve.Affine.hasPrincipalDivisors_of_isAlgClosed W.toAffine
    have : CharZero ((W.fullKernelQuotient Q N).toAffine.FunctionField) :=
      charZero_of_injective_algebraMap (algebraMap H _).injective
    have hsep : SeparableAlong H ι := AlgebraicCurve.separableAlong_of_charZero ι hι
    have hN : NormFormulaAlong H ι hfin := AlgebraicCurve.normFormulaAlong ι hfin hsep
    have hkerQ := hker hN
    have hcyc : IsAddCyclic (pointMapOfPushforward ι hι hfin hN).ker := by
      rw [hkerQ]; infer_instance
    have hcard : Nat.card (pointMapOfPushforward ι hι hfin hN).ker = N := by
      rw [hkerQ, Nat.card_zmultiples]; exact hQ
    exact WeierstrassCurve.Affine.eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward
      H W.toAffine (W.fullKernelQuotient Q N).toAffine ι hι hfin hN N hcyc hcard data
  · exact fullKernelIsRootAt_of_odd N hO

theorem fullKernelDiscAt_of_tower
    (hevD : ∀ (N : ℕ) [NeZero N], Even N → FullKernelDiscAt N) (N : ℕ) [NeZero N] :
    FullKernelDiscAt N := by
  rcases Nat.even_or_odd N with hE | hO
  · exact hevD N hE
  · exact fullKernelDiscAt_of_odd N hO

end ModularCurve.TatePoint

end

namespace ModularCurve p2m_export "ModularCurve" "TatePoint.FullKernelIsRootAt" namespace TatePoint p2m_export "ModularCurve.TatePoint" "FullKernelIsRootAt FullKernelDiscAt isAlgClosed_H charZero_H H fullKernelIsRootAt_of_odd fullKernelDiscAt_of_odd" end ModularCurve.TatePoint
p2m_open_scoped "ModularCurve ModularCurve.TatePoint" in

private theorem ModularCurve.TatePoint.fullKernelIsRootAt_aux
    (N : ℕ) [NeZero N] : ModularCurve.TatePoint.FullKernelIsRootAt N :=
  ModularCurve.TatePoint.fullKernelIsRootAt_of_tower N

#check @ModularCurve.TatePoint.fullKernelIsRootAt_of_tower
#check @ModularCurve.TatePoint.fullKernelDiscAt_of_tower
#check @ModularCurve.TatePoint.fullKernelIsRootAt_aux

open scoped Classical
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_TatePoint_fullKernelIsRootAt.ModularCurve _root_.ModularCurve.TatePoint _root_.P2MW.S_ModularCurve_TatePoint_fullKernelIsRootAt.ModularCurve.TatePoint in

theorem solution (N : ℕ) [NeZero N] : FullKernelIsRootAt N :=
  ModularCurve.TatePoint.fullKernelIsRootAt_aux N

#print axioms solution

end S_ModularCurve_TatePoint_fullKernelIsRootAt
end P2MW
export P2MW.S_ModularCurve_TatePoint_fullKernelIsRootAt (solution)
