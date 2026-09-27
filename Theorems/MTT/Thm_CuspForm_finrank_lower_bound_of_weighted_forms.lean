import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.LinearAlgebra.Dimension.Finite
open UpperHalfPlane
open scoped MatrixGroups
theorem CuspForm.finrank_lower_bound_of_weighted_forms
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] {d r k : ℕ} (hd : 0 < d) (hr : r ≤ k)
    (A : ModularForm Γ 1) (B : ModularForm Γ (d : ℤ)) (D : CuspForm Γ (r : ℤ))
    (h : ℝ) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (hA : (qExpansion h A).order = 0) (hB : (qExpansion h B).order = 1) (hD : D ≠ 0)
    [FiniteDimensional ℂ (CuspForm Γ (k : ℤ))] :
    (k - r) / d + 1 ≤ Module.finrank ℂ (CuspForm Γ (k : ℤ)) := by sorry
