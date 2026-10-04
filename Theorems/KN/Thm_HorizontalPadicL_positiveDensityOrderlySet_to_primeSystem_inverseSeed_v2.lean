import Definitions.KN.Def_KN_SeededPrimeGaloisDataV2
import Definitions.KN.Def_KN_InverseSeedConventionV2

namespace HorizontalPadicL

theorem positiveDensityOrderlySet_to_primeSystem_inverseSeed_v2
    {N k p m B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {f : MTT.Eigenform N k ι} {η : DirichletCharacterWithLevel}
    {V : SeededEigenformPadicPlaceData (p := p) f η}
    (hm : 0 < m)
    (D : SeededOrderlyFrobeniusClassData f η m B V)
    (δ : ℝ) (hδ : 0 < δ)
    (hdensity : HasPrimeNaturalDensity D.primes δ)
    (horderly : ∀ ⦃ℓ : ℕ⦄, ℓ ∈ D.primes →
      IsOrderlyPrimeForSeededEigenformV3 p m V.embedding f η ℓ) :
    ∃ L : SeededHorizontalPrimeSystemV3 p V.embedding f η B,
      L.orderExponent = m := by sorry

end HorizontalPadicL
