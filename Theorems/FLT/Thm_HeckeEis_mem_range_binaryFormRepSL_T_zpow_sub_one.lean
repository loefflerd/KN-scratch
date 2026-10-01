import Definitions.FLT.Def_HeckeEis_BinaryFormRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
theorem HeckeEis.mem_range_binaryFormRepSL_T_zpow_sub_one {K : Type*} [Field K] [CharZero K] (n : ℕ) {h : ℤ}
    (hh : h ≠ 0) (P : ↥(HeckeEis.BinaryForm K n))
    (hP : AddMonoidAlgebra.coeff (P : MvPolynomial (Fin 2) K) (Finsupp.single 1 n) = 0) :
    P ∈ LinearMap.range (HeckeEis.binaryFormRepSL K n (ModularGroup.T ^ h) - 1) := by sorry
