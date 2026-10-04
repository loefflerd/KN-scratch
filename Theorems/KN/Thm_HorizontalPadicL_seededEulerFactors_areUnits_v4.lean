import Definitions.KN.Def_KN_SeededThetaConstructionV2B
import Definitions.KN.Def_KN_InverseSeedConventionV2

noncomputable section

namespace HorizontalPadicL

/-- The orderly-prime calculation makes every Euler factor in the faithful
theta system a unit. -/
theorem seededEulerFactors_areUnits_v4
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (hnew : IsNewEigenform f)
    (η : DirichletCharacterWithLevel) (ιp : MTT.Qbar →+* ℂ_[p])
    (L : SeededHorizontalPrimeDataV3 p ιp f η B)
    (Θ : SeededFiniteThetaDataV3 L) :
    Θ.HasUnitEulerFactors := by
  sorry

end HorizontalPadicL
