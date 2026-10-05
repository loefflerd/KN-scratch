module

public import Theorems.KN.Thm_MTT_Eigenform_p_mem_coefficientPrime

section privateSection

noncomputable section

theorem solution
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    f.coefficientPrime ιp ≠ ⊥ := by
  intro hbot
  have hp := f.p_mem_coefficientPrime ιp
  rw [hbot, Ideal.mem_bot] at hp
  exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hp
end

end privateSection

public section publicSection

noncomputable section

/-- The coefficient-field prime selected by a `p`-adic embedding is nonzero. -/
theorem MTT.Eigenform.coefficientPrime_ne_bot
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    f.coefficientPrime ιp ≠ ⊥ := _root_.solution f ιp
end

end publicSection
