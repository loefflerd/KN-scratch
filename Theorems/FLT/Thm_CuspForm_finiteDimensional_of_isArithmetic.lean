module

public import Mathlib.NumberTheory.ModularForms.QExpansion

import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Theorems.FLT.Thm_ModularForm_finiteDimensional_of_isArithmetic

section privateSection

theorem solution (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic] [𝒢.HasDetOne] (k : ℤ) : FiniteDimensional ℂ (CuspForm 𝒢 k) := by
  have := ModularForm.finiteDimensional_of_isArithmetic 𝒢 k
  exact Module.Finite.of_injective CuspForm.toModularFormₗ CuspForm.toModularFormₗ_injective

end privateSection

public section publicSection

open UpperHalfPlane
open scoped MatrixGroups
theorem CuspForm.finiteDimensional_of_isArithmetic (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic] [𝒢.HasDetOne] (k : ℤ) : FiniteDimensional ℂ (CuspForm 𝒢 k) :=
  solution 𝒢 k

end publicSection
