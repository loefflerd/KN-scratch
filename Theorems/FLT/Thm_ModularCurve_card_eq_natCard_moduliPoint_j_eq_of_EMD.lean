import Definitions.FLT.Def_ModularCurve_EMD

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.card_eq_natCard_moduliPoint_j_eq_of_EMD (N : ℕ) [NeZero N]
    (j₀ : AlgebraicClosure ℚ) (hEMD : ModularCurve.EMD N j₀)
    (S : Finset (AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N)))
    (hS : ∀ v, v ∈ S ↔ 0 < v.ord (ModularCurve.jBar N - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) j₀)) :
    S.card = Nat.card {x : ModularCurve.ModuliPoint N (AlgebraicClosure ℚ) // ModularCurve.ModuliPoint.j x = j₀} := by sorry
