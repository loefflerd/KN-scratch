import Definitions.KN.Def_MTT_EigenformCoefficientPrime

set_option autoImplicit false
noncomputable section

theorem solution
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    (f.coefficientPrime ιp).IsPrime := by
  rw [MTT.Eigenform.coefficientPrime]
  let _ := (IsLocalRing.maximalIdeal.isMaximal (𝓞_ℂ_[p])).isPrime
  exact Ideal.IsPrime.comap _
