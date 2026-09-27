import Definitions.FLT.Def_ModularCurve_EMD

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.finite_cycSub (N : ℕ) [NeZero N] (E₀ : WeierstrassCurve (AlgebraicClosure ℚ)) [E₀.IsElliptic] :
    Finite (CycSub E₀ N) := by sorry
