import Definitions.KN.Def_KN_SeededFiniteThetaCriticalZeroSetV2
import Definitions.KN.Def_KN_InverseSeedConventionV2

noncomputable section

namespace HorizontalPadicL

/-- A finite theta system whose one-coordinate transition factors are units
can be normalized along a cofinal chain of finite subsets.  The resulting
compatible horizontal measure differs at every finite-order character from
the corresponding theta evaluation by a unit, and hence has the same zeroes. -/
theorem unitNormRelationThetaSystem_to_normalizedMeasure_inverseSeed_v2
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (Θ : SeededFiniteThetaDataV3 L)
    (hnorm : Θ.SatisfiesNormRelations)
    (hunit : Θ.HasUnitEulerFactors)
    (hzero : Θ.HasSeededCriticalZeroSet) :
    ∃ μ : SeededNormalizedThetaMeasureV3 L,
      μ.characters = Θ.characters ∧
      μ.InterpolatesSeededCriticalValues := by
  sorry

end HorizontalPadicL
