module

public import Definitions.KN.Def_KN_EigenformResidualGaloisRepresentationV2
public import Mathlib.NumberTheory.NumberField.Discriminant.Different

section privateSection

noncomputable section

namespace HorizontalPadicL

open NumberField Ideal FrobeniusDensity

theorem _root_.solution
    {N k p : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hk : 2 ≤ k)
    {ι : MTT.Qbar →+* ℂ}
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p])
    (D : EigenformResidualGaloisRepresentationData hN hk f ιp) :
    letI : Field D.kernelField := D.kernelField_field
    letI : NumberField D.kernelField := D.kernelField_numberField
    ∀ {l : ℕ}, l.Prime →
      (l : ℤ) ∣ NumberField.discr D.kernelField → l ∣ N * p := by
  let K := D.kernelField
  let : Field K := D.kernelField_field
  have : NumberField K := D.kernelField_numberField
  have : IsGalois ℚ K := D.kernelField_galois
  intro l hl hldisc
  by_contra hldvd
  have hlcop : Nat.Coprime l (N * p) :=
    hl.coprime_iff_not_dvd.mpr hldvd
  have hnotdisc : ¬ (l : ℤ) ∣ NumberField.discr K := by
    rw [NumberField.not_dvd_discr_iff_forall_liesOver K (𝓞 K)
      (Nat.prime_iff_prime_int.mp hl)]
    intro Q hQmax hQover
    have : Fact l.Prime := ⟨hl⟩
    have : Q.IsPrime := hQmax.isPrime
    have : Q.LiesOver (ratPrimeIdeal l) := hQover
    have hI : Q.inertia (K ≃ₐ[ℚ] K) = ⊥ :=
      D.unramified_outside hl hlcop Q inferInstance inferInstance
    rw [← Ideal.ramificationIdx_eq_one_iff,
      ← Ideal.ramificationIdxIn_eq_ramificationIdx
        (ratPrimeIdeal l) Q (K ≃ₐ[ℚ] K),
      ← Ideal.card_inertia_eq_ramificationIdxIn
        (G := K ≃ₐ[ℚ] K) (ratPrimeIdeal l) Q,
      hI]
    simp
  exact hnotdisc hldisc

end HorizontalPadicL
end

end privateSection

public section publicSection

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
      (l : ℤ) ∣ NumberField.discr D.kernelField → l ∣ N * p := _root_.solution hN hk f ιp D

end HorizontalPadicL
end

end publicSection
