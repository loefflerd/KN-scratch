module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Determinant

import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LinearMap_charpoly_of_finrank_eq_two

open Polynomial

theorem solution {R : Type*} {M : Type*} [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] (h : Module.finrank R M = 2) (f : M →ₗ[R] M) : f.charpoly = X ^ 2 - C (LinearMap.trace R M f) * X + C (LinearMap.det f) := by
  let b := Module.finBasisOfFinrankEq R M h
  rw [← f.charpoly_toMatrix b, Matrix.charpoly_fin_two, ← LinearMap.trace_eq_matrix_trace R b f,
    LinearMap.det_toMatrix b f]

end S_LinearMap_charpoly_of_finrank_eq_two
end P2MW
export P2MW.S_LinearMap_charpoly_of_finrank_eq_two (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

theorem LinearMap.charpoly_of_finrank_eq_two {R : Type*} {M : Type*} [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] (h : Module.finrank R M = 2) (f : M →ₗ[R] M) : f.charpoly = X ^ 2 - C (LinearMap.trace R M f) * X + C (LinearMap.det f) := _root_.P2MW.S_LinearMap_charpoly_of_finrank_eq_two.solution h f

end publicSection
