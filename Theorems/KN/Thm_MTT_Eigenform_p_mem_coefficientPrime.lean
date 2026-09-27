import Definitions.KN.Def_MTT_EigenformCoefficientPrime

set_option autoImplicit false
noncomputable section

open NumberField

/-- The rational prime `p` belongs to the coefficient-field prime selected by
a `p`-adic embedding. -/
theorem MTT.Eigenform.p_mem_coefficientPrime
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    (p : 𝓞 f.coefficientField) ∈ f.coefficientPrime ιp := by
  sorry
