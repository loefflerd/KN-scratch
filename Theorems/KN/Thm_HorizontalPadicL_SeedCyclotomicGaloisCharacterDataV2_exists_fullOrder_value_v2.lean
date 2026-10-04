import Definitions.KN.Def_KN_SeedCyclotomicGaloisCharactersV3B

noncomputable section

namespace HorizontalPadicL

/-- A faithful seed/cyclotomic Galois realization supplies a residue class on
which the seed Dirichlet character has its full order. -/
theorem SeedCyclotomicGaloisCharacterDataV2.exists_fullOrder_value_v2
    {N p m : ℕ} [Fact p.Prime]
    (η : DirichletCharacterWithLevel)
    (C : SeedCyclotomicGaloisCharacterDataV2 N p m η) :
    ∃ a : (ZMod η.1.1)ˣ,
      orderOf (η.2 (a : ZMod η.1.1)) = orderOf η.2 := by sorry

end HorizontalPadicL
