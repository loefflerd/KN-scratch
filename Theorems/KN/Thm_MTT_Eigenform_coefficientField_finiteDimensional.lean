import Definitions.KN.Def_MTT_EigenformCoefficientField

set_option autoImplicit false
noncomputable section

/-- The Fourier coefficients and nebentype values of an MTT eigenform generate
a single number field inside `MTT.Qbar`. -/
theorem MTT.Eigenform.coefficientField_finiteDimensional
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) :
    FiniteDimensional ℚ f.coefficientField := by sorry
