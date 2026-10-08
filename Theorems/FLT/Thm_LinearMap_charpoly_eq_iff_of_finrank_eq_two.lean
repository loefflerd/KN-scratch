module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Determinant

import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Theorems.FLT.Thm_LinearMap_charpoly_of_finrank_eq_two
import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LinearMap_charpoly_eq_iff_of_finrank_eq_two

open Polynomial

theorem solution {R : Type*} {M : Type*} [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] (h : Module.finrank R M = 2) (f : M →ₗ[R] M) (a b : R) : f.charpoly = X ^ 2 - C a * X + C b ↔ LinearMap.trace R M f = a ∧ LinearMap.det f = b := by
  rw [LinearMap.charpoly_of_finrank_eq_two h f]
  constructor
  · intro he
    have h0 := congr_arg (fun q : R[X] ↦ q.coeff 0) he
    have h1 := congr_arg (fun q : R[X] ↦ q.coeff 1) he
    simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C] at h0 h1
    norm_num at h0 h1
    exact ⟨h1, h0⟩
  · rintro ⟨ht, hd⟩
    rw [ht, hd]

end S_LinearMap_charpoly_eq_iff_of_finrank_eq_two
end P2MW
export P2MW.S_LinearMap_charpoly_eq_iff_of_finrank_eq_two (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

theorem LinearMap.charpoly_eq_iff_of_finrank_eq_two {R : Type*} {M : Type*} [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] (h : Module.finrank R M = 2) (f : M →ₗ[R] M) (a b : R) : f.charpoly = X ^ 2 - C a * X + C b ↔ LinearMap.trace R M f = a ∧ LinearMap.det f = b := _root_.P2MW.S_LinearMap_charpoly_eq_iff_of_finrank_eq_two.solution h f a b

end publicSection
