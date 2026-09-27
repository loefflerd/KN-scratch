import Definitions.FLT.Def_ModularCurve_MazurStepThreeInputs
import Definitions.FLT.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve
theorem ModularCurve.card_eq_cuspCount_of_forall_mem_iff_ord_jBar_neg (N : ℕ) [NeZero N]
    (S : Finset (AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N)))
    (hS : ∀ v, v ∈ S ↔ v.ord (ModularCurve.jBar N) < 0) :
    S.card = ModularCurve.cuspCount N := by sorry
