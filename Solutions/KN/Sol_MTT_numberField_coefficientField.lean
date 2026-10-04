import Theorems.KN.Thm_MTT_Eigenform_coefficientField_finiteDimensional
import Mathlib.NumberTheory.NumberField.Basic

noncomputable section

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) :
    NumberField f.coefficientField := by
  let _ : FiniteDimensional ℚ f.coefficientField :=
    MTT.Eigenform.coefficientField_finiteDimensional hN hk ι f
  exact NumberField.of_module_finite ℚ f.coefficientField
