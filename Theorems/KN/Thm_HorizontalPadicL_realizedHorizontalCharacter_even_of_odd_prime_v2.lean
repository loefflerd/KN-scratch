import Definitions.KN.Def_KN_SeededInverseThetaSystemV2

noncomputable section

namespace HorizontalPadicL

/-- A realized horizontal character is even when the horizontal prime is odd:
its order is a power of `p`, while its value at `-1` has order at most two. -/
theorem realizedHorizontalCharacter_even_of_odd_prime_v2
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (R : SeededHorizontalCharacterRealizationV3 L)
    (hR : R.HasExpectedProperties) (hpodd : p ≠ 2)
    (χ : HorizontalCharacter p L.exponent) :
    (R.realized χ).2 (-1) = 1 := by
  sorry

end HorizontalPadicL
