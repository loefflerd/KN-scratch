module

public import Definitions.KN.Def_MTT_EigenformCoefficientPrime

section privateSection

noncomputable section

theorem solution
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    (f.coefficientPrime ιp).IsPrime := by
  rw [MTT.Eigenform.coefficientPrime]
  let _ := (IsLocalRing.maximalIdeal.isMaximal (𝓞_ℂ_[p])).isPrime
  exact Ideal.IsPrime.comap _
end

end privateSection

public section publicSection

noncomputable section

/-- The prime selected by a `p`-adic embedding is a prime ideal. -/
theorem MTT.Eigenform.coefficientPrime_isPrime
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    (f.coefficientPrime ιp).IsPrime := _root_.solution f ιp
end

end publicSection
