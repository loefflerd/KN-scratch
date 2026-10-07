module

public import Definitions.FLT.Def_TaylorWiles_Primes
public import Definitions.KN.Def_MTT_EigenformCoefficientResidueField
public import Theorems.KN.Thm_MTT_Eigenform_coeff_mem_ringOfIntegers
public import Theorems.KN.Thm_MTT_Eigenform_nebentype_mem_ringOfIntegers
public import Mathlib.NumberTheory.NumberField.Ideal.Basic

@[expose] public section publicSection

noncomputable section

open NumberField

namespace MTT.Eigenform

/-- A Fourier coefficient, regarded as an algebraic integer in the
coefficient field. -/
def integralCoeff
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) {ι : MTT.Qbar →+* ℂ}
    (f : MTT.Eigenform N k ι) (n : ℕ) : 𝓞 f.coefficientField :=
  ⟨⟨f.coeff n, f.coeff_mem_coefficientField n⟩,
    MTT.Eigenform.coeff_mem_ringOfIntegers hN hk ι f n⟩

/-- A nebentype value, regarded as an algebraic integer in the coefficient
field. -/
def integralNebentype
    {N k : ℕ} {ι : MTT.Qbar →+* ℂ} (f : MTT.Eigenform N k ι)
    (a : ZMod N) : 𝓞 f.coefficientField :=
  ⟨⟨f.epsilon a, f.nebentype_mem_coefficientField a⟩,
    f.nebentype_mem_ringOfIntegers a⟩

end MTT.Eigenform

namespace HorizontalPadicL

open NumberField Ideal FrobeniusDensity

/-- The residue field of the coefficient field at the place selected by
`ιp`.  Both the coefficient ring and its prime ideal are canonical. -/
abbrev EigenformResidueField
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :=
  f.coefficientResidueField ιp

/-- The textbook residual Galois representation attached to a normalized
eigenform at a chosen `p`-adic place.

The coefficient ring is canonically the integer ring of the coefficient
field.  The prime is `f.coefficientPrime ιp`, selected by the chosen
embedding into `ℂ_[p]`, and the representation takes values in the canonical
residue ring `EigenformResidueField f ιp`.  Its field and finiteness
structures are derived from the coefficient-field and coefficient-prime
theorems, so finiteness of the image is a theorem rather than additional
data. -/
structure EigenformResidualGaloisRepresentationData
    {N k p : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) : Type 2 where
  kernelField : Type
  [kernelField_field : Field kernelField]
  [kernelField_numberField : NumberField kernelField]
  [kernelField_galois : IsGalois ℚ kernelField]
  representation :
    (kernelField ≃ₐ[ℚ] kernelField) →*
      Matrix (Fin 2) (Fin 2) (EigenformResidueField f ιp)
  faithful : Function.Injective representation
  unramified_outside : ∀ ⦃l : ℕ⦄, l.Prime → Nat.Coprime l (N * p) →
    ∀ (Q : Ideal (𝓞 kernelField)), Q.IsPrime →
      Q.LiesOver (ratPrimeIdeal l) →
      Q.inertia (kernelField ≃ₐ[ℚ] kernelField) = ⊥
  trace_frobenius : ∀ ⦃l : ℕ⦄, (hl : l.Prime) →
    Nat.Coprime l (N * p) →
    ∀ (Q : Ideal (𝓞 kernelField)) (_ : Q.IsPrime)
      (_ : Q.LiesOver (ratPrimeIdeal l)),
      haveI : Finite ((𝓞 kernelField) ⧸ Q) :=
        finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hl)
      Matrix.trace
          (representation
            (arithFrobAt ℤ (kernelField ≃ₐ[ℚ] kernelField) Q)) =
        Ideal.Quotient.mk (f.coefficientPrime ιp) (f.integralCoeff hN hk l)
  det_frobenius : ∀ ⦃l : ℕ⦄, (hl : l.Prime) →
    Nat.Coprime l (N * p) →
    ∀ (Q : Ideal (𝓞 kernelField)) (_ : Q.IsPrime)
      (_ : Q.LiesOver (ratPrimeIdeal l)),
      haveI : Finite ((𝓞 kernelField) ⧸ Q) :=
        finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hl)
      Matrix.det
          (representation
            (arithFrobAt ℤ (kernelField ≃ₐ[ℚ] kernelField) Q)) =
        Ideal.Quotient.mk (f.coefficientPrime ιp)
          (f.integralNebentype (l : ZMod N) *
            (l : 𝓞 f.coefficientField) ^ (k - 1))

end HorizontalPadicL
end

end publicSection
