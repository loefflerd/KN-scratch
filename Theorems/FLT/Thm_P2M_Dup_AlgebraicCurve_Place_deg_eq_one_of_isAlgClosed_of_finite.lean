module

public import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Definitions.FLT.Def_AlgebraicCurve_IsCurveOver

import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed_of_finite

open AlgebraicCurve

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] (v : Place K F)
    [Module.Finite K v.ResidueField] : v.deg = 1 := by
  have : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  have hbij : Function.Bijective (algebraMap K v.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  show Module.finrank K v.ResidueField = 1
  rw [← Module.finrank_self K]
  exact ((AlgEquiv.ofBijective (Algebra.ofId K v.ResidueField) hbij).toLinearEquiv.finrank_eq).symm

end S_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed_of_finite
end P2MW
export P2MW.S_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed_of_finite (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
theorem P2M.Dup.AlgebraicCurve.Place.deg_eq_one_of_isAlgClosed_of_finite
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] (v : Place K F)
    [Module.Finite K v.ResidueField] : v.deg = 1 := _root_.P2MW.S_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed_of_finite.solution v

end publicSection
