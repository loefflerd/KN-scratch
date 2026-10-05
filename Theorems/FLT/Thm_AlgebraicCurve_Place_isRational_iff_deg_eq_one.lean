module

public import Definitions.FLT.Def_AlgebraicCurve_PlaceEvaluation

import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_isRational_iff_deg_eq_one

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) : v.IsRational ↔ v.deg = 1 := by
  constructor
  · intro hv
    have hbij : Function.Bijective (algebraMap K v.ResidueField) :=
      ⟨v.algebraMap_residueField_injective, hv⟩
    show Module.finrank K v.ResidueField = 1
    rw [← Module.finrank_self K]
    exact ((AlgEquiv.ofBijective (Algebra.ofId K v.ResidueField) hbij).toLinearEquiv.finrank_eq).symm
  · intro h x
    have hbot : (⊥ : Subalgebra K v.ResidueField) = ⊤ :=
      Subalgebra.bot_eq_top_iff_finrank_eq_one.mpr h
    have hx : x ∈ (⊥ : Subalgebra K v.ResidueField) := by
      rw [hbot]
      exact Algebra.mem_top
    exact Algebra.mem_bot.mp hx

end S_AlgebraicCurve_Place_isRational_iff_deg_eq_one
end P2MW
export P2MW.S_AlgebraicCurve_Place_isRational_iff_deg_eq_one (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
theorem AlgebraicCurve.Place.isRational_iff_deg_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) : v.IsRational ↔ v.deg = 1 := _root_.P2MW.S_AlgebraicCurve_Place_isRational_iff_deg_eq_one.solution v

end publicSection
