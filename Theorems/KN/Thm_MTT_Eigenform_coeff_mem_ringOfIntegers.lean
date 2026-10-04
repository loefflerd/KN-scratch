import Definitions.KN.Def_MTT_EigenformCoefficientField
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

noncomputable section

/-- Every Fourier coefficient, regarded as an element of the coefficient
field, belongs to its ring of integers. -/
theorem MTT.Eigenform.coeff_mem_ringOfIntegers
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) (n : ℕ) :
    (⟨f.coeff n, f.coeff_mem_coefficientField n⟩ : f.coefficientField) ∈
      integralClosure ℤ f.coefficientField := by sorry
