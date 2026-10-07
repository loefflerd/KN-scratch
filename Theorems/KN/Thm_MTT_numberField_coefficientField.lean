module

public import Definitions.KN.Def_MTT_EigenformCoefficientField
public import Mathlib.NumberTheory.NumberField.Basic

import Theorems.KN.Thm_MTT_Eigenform_coefficientField_finiteDimensional

section privateSection

noncomputable section

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) :
    NumberField f.coefficientField := by
  let _ : FiniteDimensional ℚ f.coefficientField :=
    MTT.Eigenform.coefficientField_finiteDimensional hN hk ι f
  exact NumberField.of_module_finite ℚ f.coefficientField
end

end privateSection

public section publicSection

noncomputable section

theorem MTT.numberField_coefficientField
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) :
    NumberField f.coefficientField := _root_.solution hN hk ι f
end

end publicSection
