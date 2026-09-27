import Definitions.KN.Def_KN_SeedCyclotomicGaloisCharactersV3B

set_option autoImplicit false

namespace HorizontalPadicL

/-- Disjoint ramification between the residual/cyclotomic extension and the
seed-character extension gives a simultaneous seeded Frobenius class. -/
theorem disjointRamification_seededFrobeniusClass_exists_v4
    {N k p : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hk : 2 ≤ k) (heven : Even k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (η : DirichletCharacterWithLevel)
    (m B : ℕ) (hB : 0 < B)
    (hηcoprime : Nat.Coprime (N * p) η.2.conductor)
    (V : SeededEigenformPadicPlaceData (p := p) f η)
    (R : ResidualEigenformRepresentationData f η V)
    (C : SeedCyclotomicGaloisCharacterDataV2 N p m η) :
    Nonempty (SeededOrderlyFrobeniusClassData f η m B V) := by sorry

end HorizontalPadicL
