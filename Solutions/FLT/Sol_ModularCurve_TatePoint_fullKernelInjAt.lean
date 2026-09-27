import Definitions.FLT.Def_ModularCurve_CycSubRootBridgeN
import Definitions.FLT.Def_Isogeny_ConditionalCurrency
import Definitions.FLT.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Theorems.FLT.Thm_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_abelTheorem
import Theorems.FLT.Thm_AlgebraicCurve_normFormulaAlong
import Theorems.FLT.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.FLT.Thm_WeierstrassCurve_Affine_ker_pointMapOfPushforward_eq_of_j_eq_of_forall_pointEnd_eq_zsmul
import Theorems.FLT.Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_forall_pointEnd_eq_zsmul_of_transcendental_j
import Theorems.FLT.Thm_WeierstrassCurve_Affine_forall_normFormulaAlong_of_isAlgClosed_of_charZero
import Theorems.FLT.Thm_WeierstrassCurve_exists_functionFieldHom_fullKernelQuotient_pointMapOfPushforward_ker_eq_zmultiples
import Theorems.FLT.Thm_WeierstrassCurve_Affine_hasPrincipalDivisors_of_isAlgClosed
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_TatePoint_fullKernelInjAt
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap2_zero"

set_option autoImplicit false

open ModularCurve ModularCurve.TatePoint WeierstrassCurve AlgebraicCurve

namespace KernelTower

theorem transcendental_rat_irrel {K : Type*} [Field K] {i₁ i₂ : Algebra ℚ K} {x : K}
    (h : @Transcendental ℚ K _ _ i₁ x) : @Transcendental ℚ K _ _ i₂ x := by
  have hi : i₁ = i₂ := Subsingleton.elim _ _
  subst hi
  exact h

theorem charZero_functionField {F : Type*} [Field F] [CharZero F] (V : WeierstrassCurve F) :
    CharZero V.toAffine.FunctionField :=
  charZero_of_injective_algebraMap (algebraMap F V.toAffine.FunctionField).injective

private theorem fullKernelInjAt' (N : ℕ) [NeZero N] : FullKernelInjAt N := by
  intro _ W _ ht Q Q' hQ hQ' hΔ hΔ' hj
  letI := isAlgClosed_H
  letI := charZero_H

  haveI hV : (W.fullKernelQuotient Q N).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  haveI hV' : (W.fullKernelQuotient Q' N).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ'⟩

  obtain ⟨gW, hcW, hAW⟩ :=
    WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_abelTheorem W.toAffine
  letI := gW
  haveI := hcW
  haveI := hAW
  obtain ⟨gV, hcV, hAV⟩ := WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_abelTheorem
    (W.fullKernelQuotient Q N).toAffine
  letI := gV
  haveI := hcV
  haveI := hAV
  obtain ⟨gV', hcV', hAV'⟩ := WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_abelTheorem
    (W.fullKernelQuotient Q' N).toAffine
  letI := gV'
  haveI := hcV'
  haveI := hAV'

  obtain ⟨ι, hι, hfin, hker⟩ :=
    WeierstrassCurve.exists_functionFieldHom_fullKernelQuotient_pointMapOfPushforward_ker_eq_zmultiples
      (W := W) (Q := Q) (N := N) hQ hΔ
  obtain ⟨ι', hι', hfin', hker'⟩ :=
    WeierstrassCurve.exists_functionFieldHom_fullKernelQuotient_pointMapOfPushforward_ker_eq_zmultiples
      (W := W) (Q := Q') (N := N) hQ' hΔ'

  haveI := WeierstrassCurve.Affine.hasPrincipalDivisors_of_isAlgClosed W.toAffine
  haveI := charZero_functionField (W.fullKernelQuotient Q N)
  haveI := charZero_functionField (W.fullKernelQuotient Q' N)
  have hN : AlgebraicCurve.NormFormulaAlong H ι hfin :=
    AlgebraicCurve.normFormulaAlong ι hfin (AlgebraicCurve.separableAlong_of_charZero ι hι)
  have hN' : AlgebraicCurve.NormFormulaAlong H ι' hfin' :=
    AlgebraicCurve.normFormulaAlong ι' hfin' (AlgebraicCurve.separableAlong_of_charZero ι' hι')

  have hNs :=
    WeierstrassCurve.Affine.forall_normFormulaAlong_of_isAlgClosed_of_charZero W.toAffine
  have hE : ∀ D : WeierstrassCurve.Affine.IsogenyEndDatum W.toAffine,
      ∃ m : ℤ, ∀ P : W.toAffine.Point, D.pointEnd (hNs D) P = m • P :=
    fun D => WeierstrassCurve.Affine.IsogenyEndDatum.exists_forall_pointEnd_eq_zsmul_of_transcendental_j
      W hNs (transcendental_rat_irrel ht) D

  have hcard : Nat.card (WeierstrassCurve.Affine.pointMapOfPushforward ι hι hfin hN).ker
      = Nat.card (WeierstrassCurve.Affine.pointMapOfPushforward ι' hι' hfin' hN').ker := by
    rw [hker hN, hker' hN', Nat.card_zmultiples, Nat.card_zmultiples, hQ, hQ']

  have hkk :=
    WeierstrassCurve.Affine.ker_pointMapOfPushforward_eq_of_j_eq_of_forall_pointEnd_eq_zsmul W hNs hE
      (W.fullKernelQuotient Q N) (W.fullKernelQuotient Q' N) ι hι hfin hN ι' hι' hfin' hN' hcard hj
  rw [hker hN, hker' hN'] at hkk
  exact hkk

end KernelTower

open scoped Classical
open ModularCurve ModularCurve.TatePoint in

theorem solution (N : ℕ) [NeZero N] : FullKernelInjAt N :=
  KernelTower.fullKernelInjAt' N

#print axioms solution

end S_ModularCurve_TatePoint_fullKernelInjAt
end P2MW
export P2MW.S_ModularCurve_TatePoint_fullKernelInjAt (solution)
