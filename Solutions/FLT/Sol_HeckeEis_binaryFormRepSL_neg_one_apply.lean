import Definitions.FLT.Def_HeckeEis_BinaryFormRep
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_binaryFormRepSL_neg_one_apply

open scoped MatrixGroups

open HeckeEis MvPolynomial in
theorem solution (K : Type*) [CommRing K] (n : ℕ) (P : ↥(HeckeEis.BinaryForm K n)) :
    HeckeEis.binaryFormRepSL K n (-1) P = ((-1 : K) ^ n) • P := by
  classical
  apply Subtype.ext
  rw [binaryFormRepSL_apply_coe, Submodule.coe_smul]
  have hhom : (P : MvPolynomial (Fin 2) K).IsHomogeneous n := (mem_homogeneousSubmodule n _).mp P.2
  have h0 : binarySubst K ((-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (X 0) = -X 0 := by
    rw [binarySubst_X]; simp [Matrix.one_apply]
  have h1 : binarySubst K ((-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (X 1) = -X 1 := by
    rw [binarySubst_X]; simp [Matrix.one_apply]
  conv_lhs => rw [(P : MvPolynomial (Fin 2) K).as_sum]
  conv_rhs => rw [(P : MvPolynomial (Fin 2) K).as_sum]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdn : d.degree = n := by
    by_contra hc
    exact (mem_support_iff.mp hd) (hhom.coeff_eq_zero hc)
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdn
  have hC : C ((-1 : K) ^ n) = (-1 : MvPolynomial (Fin 2) K) ^ (d 0) * (-1) ^ (d 1) := by
    rw [map_pow, map_neg, map_one, ← pow_add, hdn]
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two, map_mul, binarySubst_C,
    map_mul, map_pow, map_pow, h0, h1, smul_eq_C_mul, hC,
    neg_pow (X 0 : MvPolynomial (Fin 2) K), neg_pow (X 1 : MvPolynomial (Fin 2) K)]
  ring

end S_HeckeEis_binaryFormRepSL_neg_one_apply
end P2MW
export P2MW.S_HeckeEis_binaryFormRepSL_neg_one_apply (solution)
