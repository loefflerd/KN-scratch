import Definitions.KN.Def_KN_SeededThetaFullSupportInterpolationV3

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- Full-conductor Birch--Mellin interpolation descends through redundant
support.  The norm relations compare the two theta evaluations, and unit Euler
factors ensure that the comparison factor is nonzero. -/
theorem fullSupportCriticalZeroSet_descends_inverseSeed_v3
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (Θ : SeededFiniteThetaDataV3 L)
    (hcharacters : Θ.characters.HasExpectedProperties)
    (hnorm : Θ.SatisfiesNormRelations)
    (hunit : Θ.HasUnitEulerFactors)
    (hfull : Θ.HasFullSupportCriticalZeroSetV2) :
    Θ.HasSeededCriticalZeroSet := by
  sorry

end HorizontalPadicL
