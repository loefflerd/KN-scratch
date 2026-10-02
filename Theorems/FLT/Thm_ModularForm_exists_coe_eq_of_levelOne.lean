module

public import Mathlib.NumberTheory.ModularForms.Basic

section privateSection

open UpperHalfPlane
open scoped MatrixGroups

theorem solution
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) {k : ℤ}
    (F : ModularForm 𝒮ℒ k) :
    ∃ G : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k,
      (G : ℍ → ℂ) = (F : ℍ → ℂ) := by
  have hle : ((Γ : Subgroup (GL (Fin 2) ℝ))) ≤ 𝒮ℒ := by
    rintro _ ⟨γ, -, rfl⟩
    exact ⟨γ, rfl⟩
  refine ⟨{ toFun := F
            slash_action_eq' := fun γ hγ => F.slash_action_eq' γ (hle hγ)
            holo' := F.holo'
            bdd_at_cusps' := fun hc => F.bdd_at_cusps' (hc.mono hle) }, rfl⟩

end privateSection

public section publicSection

open UpperHalfPlane
open scoped MatrixGroups
theorem ModularForm.exists_coe_eq_of_levelOne
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) {k : ℤ}
    (F : ModularForm 𝒮ℒ k) :
    ∃ G : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k, (G : ℍ → ℂ) = (F : ℍ → ℂ) :=
  solution Γ F

end publicSection
