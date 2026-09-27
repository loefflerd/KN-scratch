import Definitions.FLT.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.modularFunctionField_eq_full_of (N : ℕ) [NeZero N] (hstep : ∀ (M : ℕ) [NeZero M] (p : ℕ), p.Prime → M * p = N → jqN M ∈ modularFunctionField N) (hgen' : ∀ (M : ℕ) [NeZero M] (p : ℕ), p.Prime → M * p = N → modularFunctionField M = modularFunctionFieldFull M) : modularFunctionField N = modularFunctionFieldFull N := by sorry
