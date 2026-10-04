import Definitions.KN.Def_KN_SeedCyclotomicGaloisCharactersV3B

noncomputable section

namespace HorizontalPadicL

theorem _root_.solution
    {N p m : ℕ} [Fact p.Prime]
    (η : DirichletCharacterWithLevel)
    (C : SeedCyclotomicGaloisCharacterDataV2 N p m η) :
    ∃ a : (ZMod η.1.1)ˣ,
      orderOf (η.2 (a : ZMod η.1.1)) = orderOf η.2 := by
  obtain ⟨a, ha⟩ := C.only_seed_values C.seedGenerator
  refine ⟨a, ?_⟩
  rw [← C.seedGenerator_order, ← orderOf_units]
  exact congrArg orderOf ha.symm

end HorizontalPadicL
