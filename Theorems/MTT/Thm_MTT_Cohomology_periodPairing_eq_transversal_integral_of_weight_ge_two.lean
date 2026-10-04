import Definitions.MTT.Def_MTT_PeriodPairing
import Mathlib.NumberTheory.ModularForms.Bounds

noncomputable section
open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Modular ComplexConjugate
open MTT.Cohomology
theorem MTT.Cohomology.periodPairing_eq_transversal_integral_of_weight_ge_two
    {N k : ℕ} (hk : 2 ≤ k)
    (f q : CuspForm (MTT.GammaOne N) (k : ℤ))
    (R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hR : Subgroup.IsComplement
      (CongruenceSubgroup.Gamma1 N : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
      (R : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)))
    (D : ℂ → ℂ)
    (hint : ∀ σ ∈ R, IntegrableOn D
      ((fun τ : ℍ ↦ ((σ • τ : ℍ) : ℂ)) '' 𝒟) volume)
    (hD : ∀ z : ℍ, D z =
      periodContraction (k - 2)
        (f z • periodPower (k - 2) (z : ℂ))
        (conj (q z) • periodPower (k - 2) (conj (z : ℂ)))) :
    periodPairing N (k - 2) f q =
      ∑ σ ∈ R, ∫ z in (fun τ : ℍ ↦ ((σ • τ : ℍ) : ℂ)) '' 𝒟, D z := by sorry
