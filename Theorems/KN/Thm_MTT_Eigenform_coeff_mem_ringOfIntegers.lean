module

public import Definitions.KN.Def_MTT_EigenformCoefficientField
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

import Theorems.KN.Thm_MTT_Eigenform_coeff_isIntegral
import Mathlib.Algebra.Algebra.Hom.Rat

section privateSection

noncomputable section

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) (n : ℕ) :
    (⟨f.coeff n, f.coeff_mem_coefficientField n⟩ : f.coefficientField) ∈
      integralClosure ℤ f.coefficientField := by
  rw [mem_integralClosure_iff]
  let inclQ : f.coefficientField →ₐ[ℚ] MTT.Qbar :=
    f.coefficientField.subtype.toRatAlgHom
  let inclZ : f.coefficientField →ₐ[ℤ] MTT.Qbar := inclQ.restrictScalars ℤ
  apply (isIntegral_algHom_iff inclZ inclZ.injective).mp
  change IsIntegral ℤ (f.coeff n)
  exact MTT.Eigenform.coeff_isIntegral hN hk ι f n
end

end privateSection

public section publicSection

noncomputable section

/-- Every Fourier coefficient, regarded as an element of the coefficient
field, belongs to its ring of integers. -/
theorem MTT.Eigenform.coeff_mem_ringOfIntegers
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) (n : ℕ) :
    (⟨f.coeff n, f.coeff_mem_coefficientField n⟩ : f.coefficientField) ∈
      integralClosure ℤ f.coefficientField := _root_.solution hN hk ι f n
end

end publicSection
