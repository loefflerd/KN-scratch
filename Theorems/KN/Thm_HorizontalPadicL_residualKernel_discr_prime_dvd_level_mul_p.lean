import Definitions.KN.Def_KN_EigenformResidualGaloisRepresentationV2
import Mathlib.NumberTheory.NumberField.Discriminant.Different

noncomputable section

namespace HorizontalPadicL

/-- Every rational prime dividing the discriminant of the kernel field of an
eigenform's residual Galois representation divides the product of the modular
level and the residue characteristic. -/
theorem residualKernel_discr_prime_dvd_level_mul_p
    {N k p : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hk : 2 ≤ k)
    {ι : MTT.Qbar →+* ℂ}
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p])
    (D : EigenformResidualGaloisRepresentationData hN hk f ιp) :
    letI : Field D.kernelField := D.kernelField_field
    letI : NumberField D.kernelField := D.kernelField_numberField
    ∀ {l : ℕ}, l.Prime →
      (l : ℤ) ∣ NumberField.discr D.kernelField → l ∣ N * p := by sorry

end HorizontalPadicL
