import Definitions.KN.Def_KN_SeededPrimeGaloisDataV2
import Definitions.KN.Def_KN_InverseSeedConventionV2

namespace HorizontalPadicL

theorem seededFrobeniusClass_isOrderly_inverseSeed_v2
    {N k p m B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {f : MTT.Eigenform N k ι} {η : DirichletCharacterWithLevel}
    {V : SeededEigenformPadicPlaceData (p := p) f η}
    (D : SeededOrderlyFrobeniusClassData f η m B V)
    (hηorder : 2 ≤ orderOf η.2)
    (horderCoprime : Nat.Coprime (orderOf η.2) p) :
    ∀ ⦃ℓ : ℕ⦄, ℓ ∈ D.primes →
      IsOrderlyPrimeForSeededEigenformV3 p m V.embedding f η ℓ := by sorry

end HorizontalPadicL
