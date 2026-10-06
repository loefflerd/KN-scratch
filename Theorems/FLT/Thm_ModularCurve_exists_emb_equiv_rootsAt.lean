import Definitions.FLT.Def_ModularCurve_EMD
import Definitions.FLT.Def_ModularCurve_TatePoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.exists_emb_equiv_rootsAt (N : ℕ) [NeZero N] (data : ModularCurve.ModularPolynomialData N)
    (j₀ : AlgebraicClosure ℚ) :
    ∃ e : ModularCurve.Emb N j₀ ≃ ModularCurve.TatePoint.RootsAt data (ModularCurve.TatePoint.jNear j₀),
      ∀ ψ : ModularCurve.Emb N j₀, (e ψ).1 = ψ.1 ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ N ModularCurve.jq),
        ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.jqd_mem_full N (dvd_refl N))⟩ := by sorry
