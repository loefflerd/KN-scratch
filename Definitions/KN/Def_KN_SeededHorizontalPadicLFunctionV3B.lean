import Definitions.KN.Def_KN_SeededHorizontalCharacterRealizationV2B

noncomputable section

namespace HorizontalPadicL

/-- The faithful interpolation contract for a seeded horizontal `p`-adic
L-function.  The Dirichlet characters are obtained from the actual quotient
maps used to push forward the theta elements. -/
def SeededHorizontalPadicLFunctionV2.InterpolatesSeededCriticalValuesV3
    {N k B p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (ν : SeededHorizontalPadicLFunctionV2 (B := B) p ιp f η) : Prop :=
  ∃ R : SeededHorizontalCharacterRealizationV2 ν.primes.toConstructionData,
    R.HasExpectedProperties ∧
    ∀ χ, ν.measure.eval χ ≠ 0 ↔
      let θ := primitiveProductV2 η (R.realized χ)
      @MTT.criticalLValue ι f.form
        θ.1.1 ⟨Nat.ne_of_gt θ.1.2⟩ θ.2 (k / 2 - 1) ≠ 0

/-- The one-sign seeded construction needed for Corollary 5.17.  The prime
`p` is required to be odd, so every horizontal character of `p`-power order
is even and the plus theta measure interpolates every character in the
horizontal family. -/
def HasSeededHorizontalPadicLConstructionV3
    {N k : ℕ} (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) : Prop :=
  ∀ (η : DirichletCharacterWithLevel)
    (_hηprim : η.2.IsPrimitive)
    (_hηeven : η.2 (-1) = 1)
    (p m B : ℕ) [Fact p.Prime]
    (_hpodd : p ≠ 2)
    (_hm : 0 < m) (_hB : 0 < B)
    (_hηorder : 2 ≤ orderOf η.2)
    (_horderCoprime : Nat.Coprime (orderOf η.2) p)
    (_hηcoprime : Nat.Coprime (N * p) η.2.conductor)
    (_hseedNonzero :
      @MTT.criticalLValue ι f.form
        η.1.1 ⟨Nat.ne_of_gt η.1.2⟩ η.2 (k / 2 - 1) ≠ 0),
    ∃ (ιp : MTT.Qbar →+* ℂ_[p])
      (ν : SeededHorizontalPadicLFunctionV2 (B := B) p ιp f η),
      ν.primes.orderExponent = m ∧
      ν.InterpolatesSeededCriticalValuesV3 ∧
      ν.measure.eval (trivialHorizontalCharacterV2 p ν.primes.exponent) ≠ 0

end HorizontalPadicL
