import Definitions.FLT.Def_ModularCurve_EMD
import Definitions.FLT.Def_ModularCurve_MazurStepThreeInputs
import Definitions.FLT.Def_HahnSeries_RamificationBound
import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial
theorem ModularCurve.exists_place_of_emb (N : ℕ) [NeZero N] (j₀ : AlgebraicClosure ℚ)
    (ψ : Emb N j₀) :
    ∃ (w : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) (g : ℚ), 0 < g ∧
      ∀ x : ↥(modularFunctionFieldBar N), (w.ord x : ℚ) * g = (ψ.1 x).order := by sorry
