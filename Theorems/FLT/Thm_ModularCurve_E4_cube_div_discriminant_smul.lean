module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Mathlib.NumberTheory.ModularForms.Discriminant

import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_E4_cube_div_discriminant_smul

noncomputable section

open Matrix.SpecialLinearGroup UpperHalfPlane Polynomial
open scoped MatrixGroups ModularForm OnePoint

namespace ModularCurve

theorem E4_cube_div_discriminant_smul' (γ : SL(2, ℤ)) (τ : ℍ) :
    ModularForm.E₄ (γ • τ) ^ 3 / ModularForm.discriminant (γ • τ)
      = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ := by
  have hγ : (mapGL ℝ γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have hE : ModularForm.E₄ (γ • τ) = denom (mapGL ℝ γ) τ ^ (4 : ℤ) * ModularForm.E₄ τ :=
    SlashInvariantForm.slash_action_eqn'' (ModularForm.E₄) hγ τ
  have hΔ : ModularForm.discriminant (γ • τ)
      = denom (mapGL ℝ γ) τ ^ (12 : ℤ) * ModularForm.discriminant τ := by
    have := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hγ τ
    simp only [CuspForm.coe_discriminant] at this
    exact this
  have hd : denom (mapGL ℝ γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  rw [hE, hΔ, mul_pow, ← zpow_natCast, ← zpow_mul]
  norm_num
  first
  | rw [mul_div_mul_left _ _ (zpow_ne_zero 12 hd)]
  | rw [mul_div_mul_left _ _ (pow_ne_zero 12 hd)]

end ModularCurve

end

theorem solution (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) : ModularForm.E₄ (γ • τ) ^ 3 / ModularForm.discriminant (γ • τ) = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ :=
  ModularCurve.E4_cube_div_discriminant_smul' γ τ

end S_ModularCurve_E4_cube_div_discriminant_smul
end P2MW
export P2MW.S_ModularCurve_E4_cube_div_discriminant_smul (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.E4_cube_div_discriminant_smul (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) : ModularForm.E₄ (γ • τ) ^ 3 / ModularForm.discriminant (γ • τ) = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ := _root_.P2MW.S_ModularCurve_E4_cube_div_discriminant_smul.solution γ τ

end publicSection
