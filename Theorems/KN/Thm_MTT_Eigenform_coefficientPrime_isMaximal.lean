module

public import Theorems.KN.Thm_MTT_Eigenform_coefficientPrime_isPrime
public import Theorems.KN.Thm_MTT_Eigenform_coefficientPrime_ne_bot
public import Theorems.KN.Thm_MTT_numberField_coefficientField
public import Mathlib.RingTheory.DedekindDomain.Basic

section privateSection

noncomputable section

theorem solution
    {N k p : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    (f.coefficientPrime ιp).IsMaximal := by
  let _ := MTT.numberField_coefficientField hN hk ι f
  exact (f.coefficientPrime_isPrime ιp).isMaximal
    (f.coefficientPrime_ne_bot ιp)
end

end privateSection

public section publicSection

noncomputable section

open NumberField

/-- The prime selected by a `p`-adic embedding is a maximal ideal of the
integer ring of the coefficient field. -/
theorem MTT.Eigenform.coefficientPrime_isMaximal
    {N k p : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    (f.coefficientPrime ιp).IsMaximal := _root_.solution hN hk f ιp
end

end publicSection
