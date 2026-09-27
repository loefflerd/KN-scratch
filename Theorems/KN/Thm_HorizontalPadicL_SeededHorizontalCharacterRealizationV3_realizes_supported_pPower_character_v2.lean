import Definitions.KN.Def_KN_SeededHorizontalCharacterRealizationV2B
import Definitions.KN.Def_KN_InverseSeedConventionV2

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- Every primitive `p`-power-order Dirichlet character supported on finitely
many selected horizontal primes is obtained from the corresponding horizontal
finite quotient. -/
theorem SeededHorizontalCharacterRealizationV3.realizes_supported_pPower_character_v2
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (R : SeededHorizontalCharacterRealizationV3 L)
    (ψ : DirichletCharacterWithLevel)
    (hprimitive : ψ.2.IsPrimitive)
    (horder : ∃ a : ℕ, orderOf ψ.2 = p ^ a)
    (hsupport : ∃ A : Finset ℕ,
      ψ.2.conductor ∣ L.supportModulus A) :
    ∃ χ : HorizontalCharacter p L.exponent,
      R.realized χ = ψ := by
  sorry

end HorizontalPadicL
