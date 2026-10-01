import Definitions.FLT.Def_AlgebraicCurve_DivisorPushPull
import Definitions.FLT.Def_ModularCurve_JLinePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IntermediateField AlgebraicCurve
theorem ModularCurve.exists_irreducible_ramificationIndex_eq_ord_aeval_of_restrict_ne_jLinePlaces (N : ℕ) [NeZero N] :
    letI := ModularCurve.jAdjoinAlgebra N
    ∀ [Algebra.IsIntegral ↥ℚ⟮ModularCurve.jq⟯ ↥(ModularCurve.modularFunctionField N)]
      (w : AlgebraicCurve.Place ℚ ↥(ModularCurve.modularFunctionField N)),
      w.restrict ↥ℚ⟮ModularCurve.jq⟯ ≠ ModularCurve.jLinePlace1728 →
      w.restrict ↥ℚ⟮ModularCurve.jq⟯ ≠ ModularCurve.jLinePlaceZero →
      w.restrict ↥ℚ⟮ModularCurve.jq⟯ ≠ ModularCurve.jLinePlaceInfty →
      ∃ p : Polynomial ℚ, Irreducible p ∧ p.Monic ∧ p.eval 0 ≠ 0 ∧ p.eval 1728 ≠ 0 ∧
        0 < w.ord (Polynomial.aeval (⟨ModularCurve.jq, ModularCurve.jq_mem N⟩ : ↥(ModularCurve.modularFunctionField N)) p) ∧
        (w.ramificationIndex ↥ℚ⟮ModularCurve.jq⟯ : ℤ) = w.ord (Polynomial.aeval (⟨ModularCurve.jq, ModularCurve.jq_mem N⟩ : ↥(ModularCurve.modularFunctionField N)) p) := by sorry
