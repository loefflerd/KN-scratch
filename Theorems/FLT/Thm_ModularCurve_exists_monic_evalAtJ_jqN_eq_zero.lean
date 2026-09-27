import Definitions.FLT.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.exists_monic_evalAtJ_jqN_eq_zero (N : ℕ) [NeZero N] : ∃ P : Polynomial (Polynomial ℤ), P.Monic ∧ P.eval₂ evalAtJ (jqN N) = 0 := by sorry
