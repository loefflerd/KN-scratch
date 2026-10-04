import Definitions.KN.Def_KN_SeededHorizontalCharacterRealizationV2B
import Definitions.KN.Def_KN_InverseSeedConventionV2

noncomputable section

namespace HorizontalPadicL

/-- The quotient maps `(Z/ℓₙZ)ˣ ↠ Z/p^(vₚ(ℓₙ-1))Z` can be chosen so that
every finite-order horizontal character is the pullback of an algebraic
Dirichlet character.  Primitive reduction preserves its order, and every
primitive `p`-power-order Dirichlet character supported on the selected primes
arises in this way.

This is the faithful replacement for
`seededHorizontalCharacterRealization_exists`: its conclusion includes the
actual pullback equation through the chosen quotient maps. -/
theorem seededHorizontalCharacterRealization_exists_v4
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeDataV3 p ιp f η B) :
    ∃ R : SeededHorizontalCharacterRealizationV3 L,
      R.HasExpectedProperties := by
  sorry

end HorizontalPadicL
