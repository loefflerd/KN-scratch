import Definitions.FLT.Def_HeckeEis_BinaryFormRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups
theorem HeckeEis.exists_eq_smul_X_pow_of_binaryFormRepSL_T_zpow_eq_self {R : Type*} [CommRing R] [IsDomain R] (n : ℕ)
    {h : ℤ} (hh : (h : R) ≠ 0) (hn : ∀ j : ℕ, 1 ≤ j → j ≤ n → (j : R) ≠ 0) (P : ↥(HeckeEis.BinaryForm R n))
    (hP : HeckeEis.binaryFormRepSL R n (ModularGroup.T ^ h) P = P) :
    ∃ c : R, (P : MvPolynomial (Fin 2) R) = c • MvPolynomial.X 0 ^ n := by sorry
