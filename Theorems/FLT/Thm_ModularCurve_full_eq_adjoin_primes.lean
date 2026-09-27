import Definitions.FLT.Def_ModularCurve_X0
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.full_eq_adjoin_primes (N : ℕ) [NeZero N] (hN : Squarefree N) : modularFunctionFieldFull N = IntermediateField.adjoin ℚ (insert jq {x : LaurentSeries ℚ | ∃ p ∈ N.primeFactors, ∃ _ : NeZero p, x = jqN p}) := by sorry
