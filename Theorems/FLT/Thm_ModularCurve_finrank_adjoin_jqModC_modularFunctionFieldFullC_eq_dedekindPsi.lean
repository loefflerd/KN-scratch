import Mathlib
import Definitions.FLT.Def_ModularCurve_X0ModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
    (K : Type*) [Field K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) :
    Module.finrank
        (IntermediateField.adjoin K
          ({⟨jqModC K, jqModC_mem_full K N⟩} : Set (modularFunctionFieldFullC K N)))
        (modularFunctionFieldFullC K N) = dedekindPsi N := by sorry
