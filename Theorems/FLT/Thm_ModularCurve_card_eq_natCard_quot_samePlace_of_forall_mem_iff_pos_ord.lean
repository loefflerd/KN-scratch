import Definitions.FLT.Def_ModularCurve_EMD

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.card_eq_natCard_quot_samePlace_of_forall_mem_iff_pos_ord (N : ℕ) [NeZero N]
    (j₀ : AlgebraicClosure ℚ)
    (S : Finset (AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N)))
    (hS : ∀ v, v ∈ S ↔ 0 < v.ord (ModularCurve.jBar N - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) j₀)) :
    S.card = Nat.card (Quot (fun ψ ψ' : ModularCurve.Emb N j₀ => ModularCurve.SamePlace ψ.1 ψ'.1)) := by sorry
