import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] (v : Place K F) (hv : v.deg ≠ 0) : v.deg = 1 := by
  have : Module.Finite K v.ResidueField := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hv)
  have e : K ≃ₗ[K] v.ResidueField :=
    LinearEquiv.ofBijective (Algebra.linearMap K v.ResidueField) (IsAlgClosed.algebraMap_bijective_of_isIntegral)
  unfold Place.deg
  rw [← e.finrank_eq, Module.finrank_self]

end S_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed (solution)
