import Mathlib.NumberTheory.ModularForms.QExpansion

import Definitions.FLT.Def_ModularCurve_LaurentCoeff
import Definitions.FLT.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane in
theorem ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange (N : ℕ)
    [NeZero N] (x : LaurentSeries ℂ)
    (hx : x ∈ ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) :
    ∃ (k : ℤ) (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k), h ≠ 0 ∧
      x * ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
        ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by sorry
