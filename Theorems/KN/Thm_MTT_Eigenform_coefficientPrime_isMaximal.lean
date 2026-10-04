import Theorems.KN.Thm_MTT_Eigenform_coefficientPrime_isPrime
import Theorems.KN.Thm_MTT_Eigenform_coefficientPrime_ne_bot
import Theorems.KN.Thm_MTT_numberField_coefficientField
import Mathlib.RingTheory.DedekindDomain.Basic

noncomputable section

open NumberField

/-- The prime selected by a `p`-adic embedding is a maximal ideal of the
integer ring of the coefficient field. -/
theorem MTT.Eigenform.coefficientPrime_isMaximal
    {N k p : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    (f.coefficientPrime ιp).IsMaximal := by
  sorry
