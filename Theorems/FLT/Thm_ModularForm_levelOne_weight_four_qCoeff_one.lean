module

public import Definitions.FLT.Def_FLTPrelim_Modularity
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_levelOne_weight_four_qCoeff_one
open scoped MatrixGroups

namespace ModularForm
p2m_export "ModularForm" "levelOne_weight_four_rank_one E₄_qExpansion_coeff_one E₄"
end ModularForm
p2m_open_scoped "ModularForm" in
private theorem ModularForm.levelOne_weight_four_qCoeff_one (Y : ModularForm 𝒮ℒ 4) : ModularFormClass.qCoeff ⇑Y 1 = 240 * ModularFormClass.qCoeff ⇑Y 0 := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c • ModularForm.E₄ = Y :=
    (finrank_eq_one_iff_of_nonzero' ModularForm.E₄ (EisensteinSeries.E_ne_zero _ ⟨2, rfl⟩)).mp
      (Module.rank_eq_one_iff_finrank_eq_one.mp ModularForm.levelOne_weight_four_rank_one) Y
  have hq : UpperHalfPlane.qExpansion 1 ⇑Y = c • UpperHalfPlane.qExpansion 1 ⇑ModularForm.E₄ := by
    rw [← ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c ModularForm.E₄,
      show (c • ⇑ModularForm.E₄) = ⇑Y from congrArg DFunLike.coe hc]
  have h0 : (UpperHalfPlane.qExpansion 1 ⇑ModularForm.E₄).coeff 0 = 1 :=
    EisensteinSeries.E_qExpansion_coeff_zero _ ⟨2, rfl⟩
  show (UpperHalfPlane.qExpansion 1 ⇑Y).coeff 1 = _ * (UpperHalfPlane.qExpansion 1 ⇑Y).coeff 0
  rw [hq, PowerSeries.coeff_smul, PowerSeries.coeff_smul, smul_eq_mul, smul_eq_mul, h0,
    ModularForm.E₄_qExpansion_coeff_one]
  ring

theorem solution (Y : ModularForm 𝒮ℒ 4) : ModularFormClass.qCoeff ⇑Y 1 = 240 * ModularFormClass.qCoeff ⇑Y 0 :=
  ModularForm.levelOne_weight_four_qCoeff_one Y

end S_ModularForm_levelOne_weight_four_qCoeff_one
end P2MW
export P2MW.S_ModularForm_levelOne_weight_four_qCoeff_one (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups
theorem ModularForm.levelOne_weight_four_qCoeff_one (Y : ModularForm 𝒮ℒ 4) : ModularFormClass.qCoeff ⇑Y 1 = 240 * ModularFormClass.qCoeff ⇑Y 0 := _root_.P2MW.S_ModularForm_levelOne_weight_four_qCoeff_one.solution Y

end publicSection
