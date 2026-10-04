import Definitions.KN.Def_KN_SeedCyclotomicGaloisCharactersV3B

namespace HorizontalPadicL

/-- The actual cyclotomic character modulo `p ^ m * N` and the character cut
out by the seed Dirichlet character admit a common finite Galois realization,
and the seed image contains an element of full order. -/
theorem seedCyclotomicGaloisCharacters_exist_v4
    {N p : ℕ} [Fact p.Prime]
    (hN : 0 < N) (η : DirichletCharacterWithLevel)
    (hηprim : η.2.IsPrimitive) (m : ℕ) (hm : 0 < m)
    (hηorder : 2 ≤ orderOf η.2)
    (horderCoprime : Nat.Coprime (orderOf η.2) p)
    (hηcoprime : Nat.Coprime (N * p) η.2.conductor) :
    Nonempty (SeedCyclotomicGaloisCharacterDataV2 N p m η) := by sorry

end HorizontalPadicL
