import Definitions.FLT.Def_ModularCurve_MazurStepThreeInputs
import Definitions.FLT.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve
theorem ModularCurve.sum_neg_ord_jBar_eq_dedekindPsi (N : ℕ) [NeZero N]
    (S : Finset (AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N)))
    (hS : ∀ v, v ∈ S ↔ v.ord (ModularCurve.jBar N) < 0) :
    ∑ v ∈ S, -v.ord (ModularCurve.jBar N) = ModularCurve.dedekindPsi N := by sorry
