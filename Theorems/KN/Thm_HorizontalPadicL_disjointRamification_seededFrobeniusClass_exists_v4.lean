module

public import Definitions.KN.Def_KN_SeedCyclotomicGaloisCharactersV3B

import Theorems.KN.Thm_HorizontalPadicL_eigenform_residualGaloisRepresentation_exists_v2
import Theorems.KN.Thm_HorizontalPadicL_residualKernel_discr_prime_dvd_level_mul_p
import Theorems.KN.Thm_HorizontalPadicL_SeedCyclotomicGaloisCharacterDataV2_exists_fullOrder_value_v2
import Theorems.KN.Thm_HorizontalPadicL_coprimeDiscriminant_simultaneousSeededFrobeniusClass_exists_v2

section privateSection

namespace HorizontalPadicL

theorem _root_.solution
    {N k p : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hk : 2 ≤ k) (_heven : Even k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (η : DirichletCharacterWithLevel)
    (m B : ℕ) (hB : 0 < B)
    (hηcoprime : Nat.Coprime (N * p) η.2.conductor)
    (V : SeededEigenformPadicPlaceData (p := p) f η)
    (_R : ResidualEigenformRepresentationData f η V)
    (C : SeedCyclotomicGaloisCharacterDataV2 N p m η) :
    Nonempty (SeededOrderlyFrobeniusClassData f η m B V) := by
  obtain ⟨D⟩ := eigenform_residualGaloisRepresentation_exists_v2
    hN hk ι f V.embedding
  obtain ⟨a, ha⟩ := C.exists_fullOrder_value_v2 η
  exact coprimeDiscriminant_simultaneousSeededFrobeniusClass_exists_v2
    hN hk ι f η m B hB hηcoprime V D a ha
      (residualKernel_discr_prime_dvd_level_mul_p hN hk f V.embedding D)

end HorizontalPadicL

end privateSection

public section publicSection

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
    Nonempty (SeededOrderlyFrobeniusClassData f η m B V) := _root_.solution hN hk heven ι f η m B hB hηcoprime V R C

end HorizontalPadicL

end publicSection
