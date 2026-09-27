import Definitions.FLT.Def_ModularCurve_EMD

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.emd_holds (N : ℕ) [NeZero N] (j₀ : AlgebraicClosure ℚ) :
    EMD N j₀ := by sorry
