import Theorems.KN.Thm_MTT_Eigenform_p_mem_coefficientPrime

noncomputable section

/-- The coefficient-field prime selected by a `p`-adic embedding is nonzero. -/
theorem MTT.Eigenform.coefficientPrime_ne_bot
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    f.coefficientPrime ιp ≠ ⊥ := by
  sorry
