import Definitions.KN.Def_KN_SeededFiniteThetaCriticalZeroSetV2
import Definitions.KN.Def_KN_InverseSeedConventionV2

noncomputable section

namespace HorizontalPadicL

/-- The general seeded interpolation property specializes at the trivial
horizontal character to the original primitive seed character. -/
theorem seededNormalizedThetaMeasure_trivial_interpolation_inverseSeed_v2
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (hηprim : η.2.IsPrimitive)
    (characters : SeededHorizontalCharacterRealizationV3 L)
    (hcharacters : characters.HasExpectedProperties)
    (μ : SeededNormalizedThetaMeasureV3 L)
    (hμcharacters : μ.characters = characters)
    (hinterp : μ.InterpolatesSeededCriticalValues) :
    μ.measure.eval (trivialHorizontalCharacterV2 p L.exponent) ≠ 0 ↔
      @MTT.criticalLValue ι f.form
        η.1.1 ⟨Nat.ne_of_gt η.1.2⟩ η.2 (k / 2 - 1) ≠ 0 := by
  sorry

end HorizontalPadicL
