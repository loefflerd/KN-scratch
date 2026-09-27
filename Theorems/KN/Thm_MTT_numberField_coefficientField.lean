import Definitions.KN.Def_MTT_EigenformCoefficientField
import Mathlib.NumberTheory.NumberField.Basic

set_option autoImplicit false
noncomputable section

theorem MTT.numberField_coefficientField
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) :
    NumberField f.coefficientField := by sorry
