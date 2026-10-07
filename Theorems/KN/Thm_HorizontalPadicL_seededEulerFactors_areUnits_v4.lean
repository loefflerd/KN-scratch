module

public import Definitions.KN.Def_KN_SeededThetaConstructionV2B
public import Definitions.KN.Def_KN_InverseSeedConventionV2

import Theorems.KN.Thm_HorizontalPadicL_horizontalGroupAlgebra_isUnit_of_augmentation_norm_one_v2

section privateSection

noncomputable section

open HorizontalPadicL

set_option linter.unusedVariables false in
theorem solution
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (hnew : IsNewEigenform f)
    (η : DirichletCharacterWithLevel) (ιp : MTT.Qbar →+* ℂ_[p])
    (L : SeededHorizontalPrimeDataV3 p ιp f η B)
    (Θ : SeededFiniteThetaDataV3 L) :
    Θ.HasUnitEulerFactors := by
  intro A n
  rcases Θ with ⟨R, hR, hintegral, characters, theta, eulerFactor, haug⟩
  subst R
  apply horizontalGroupAlgebra_isUnit_of_augmentation_norm_one_v2 L.exponent A
  calc
    ‖((horizontalAugmentation (eulerFactor A n) :
        (𝓞_ℂ_[p]).toSubring) : ℂ_[p])‖ =
        ‖ιp (η.2 (L.primeAt n) * f.coeff (L.primeAt n) -
          (η.2 (L.primeAt n)) ^ 2 - f.epsilon (L.primeAt n))‖ := haug A n
    _ = 1 := (L.primeAt_orderly n).2.2.2
end

end privateSection

public section publicSection

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
    Θ.HasUnitEulerFactors := _root_.solution f hnew η ιp L Θ

end HorizontalPadicL
end

end publicSection
