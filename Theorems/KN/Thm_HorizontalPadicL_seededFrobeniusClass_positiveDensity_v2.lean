import Definitions.KN.Def_KN_SeededPrimeGaloisDataV2

namespace HorizontalPadicL

theorem seededFrobeniusClass_positiveDensity_v2
    {N k p m B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {f : MTT.Eigenform N k ι} {η : DirichletCharacterWithLevel}
    {V : SeededEigenformPadicPlaceData (p := p) f η}
    (D : SeededOrderlyFrobeniusClassData f η m B V) :
    ∃ δ : ℝ, 0 < δ ∧ HasPrimeNaturalDensity D.primes δ := by sorry

end HorizontalPadicL
