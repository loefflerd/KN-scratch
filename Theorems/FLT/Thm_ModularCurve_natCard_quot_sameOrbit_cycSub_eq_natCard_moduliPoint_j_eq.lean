import Mathlib
import Definitions.FLT.Def_ModularCurve_EMD
import Definitions.FLT.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.natCard_quot_sameOrbit_cycSub_eq_natCard_moduliPoint_j_eq (N : ℕ) [NeZero N]
    (E₀ : WeierstrassCurve (AlgebraicClosure ℚ)) [E₀.IsElliptic] :
    Nat.card (Quot (fun H H' : ModularCurve.CycSub E₀ N => ModularCurve.SameOrbit E₀ H.1 H'.1))
      = Nat.card {x : ModularCurve.ModuliPoint N (AlgebraicClosure ℚ) // ModularCurve.ModuliPoint.j x = E₀.j} := by sorry
