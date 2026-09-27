import Mathlib
import Definitions.FLT.Def_ModularCurve_X1
import Definitions.FLT.Def_ModularCurve_X0ModL
import Theorems.FLT.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.FLT.Thm_ModularCurve_qExpand_image_intFormRatiosC_subset
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

theorem solution
    (K : Type*) [Field K] (M : ℕ) [NeZero M] :
    ModularCurve.modularFunctionFieldFullC K M ≤
      ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M) := by
  rw [ModularCurve.modularFunctionFieldFullC, IntermediateField.adjoin_le_iff]
  rintro x ⟨d, hd, hdM, rfl⟩
  have := hd
  refine ModularCurve.intFormRatiosC_subset K _ ?_

  have hle : CongruenceSubgroup.Gamma0 M ≤ CongruenceSubgroup.Gamma0 d := by
    intro γ hγ
    rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ ⊢
    exact (Int.natCast_dvd_natCast.mpr hdM).trans hγ
  refine ModularCurve.intFormRatiosC_mono K hle ?_

  refine ModularCurve.qExpand_image_intFormRatiosC_subset K (Γ := ⊤)
    (Γ' := CongruenceSubgroup.Gamma0 d) (Subgroup.mem_top _) d ?_
    ⟨_, ModularCurve.jqModC_mem_intFormRatiosC K ⊤, rfl⟩
  intro γ hγ
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ
  obtain ⟨c, hc⟩ := hγ
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact Matrix.SpecialLinearGroup.det_coe γ
  rw [hc] at hdet
  refine ⟨⟨!![γ 0 0, (d : ℤ) * γ 0 1; c, γ 1 1], ?_⟩, Subgroup.mem_top _, rfl, rfl, ?_, rfl⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet
  · show (d : ℤ) * c = γ 1 0
    rw [hc]

end S_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
end P2MW
export P2MW.S_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 (solution)
