import Definitions.KN.Def_MTT_EigenformCoefficientPrime

noncomputable section

/-- The prime selected by a `p`-adic embedding is a prime ideal. -/
theorem MTT.Eigenform.coefficientPrime_isPrime
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    (f.coefficientPrime ιp).IsPrime := by
  sorry
