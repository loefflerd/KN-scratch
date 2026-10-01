import Definitions.FLT.Def_HeckeEis_BinaryFormRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
theorem HeckeEis.coeff_single_one_eq_eval_of_mem_binaryForm {K : Type*} [CommRing K] {n : ℕ}
    {P : MvPolynomial (Fin 2) K} (hP : P ∈ HeckeEis.BinaryForm K n) :
    AddMonoidAlgebra.coeff P (Finsupp.single 1 n) = MvPolynomial.eval ![0, 1] P := by sorry
