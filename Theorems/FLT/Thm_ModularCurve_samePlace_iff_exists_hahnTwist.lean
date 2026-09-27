import Definitions.FLT.Def_ModularCurve_EMD
import Definitions.FLT.Def_HahnSeries_Monodromy

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.samePlace_iff_exists_hahnTwist (N : ℕ) [NeZero N]
    (j₀ : AlgebraicClosure ℚ) (ψ ψ' : Emb N j₀) :
    SamePlace ψ.1 ψ'.1 ↔
      ∃ χ ∈ HahnSeries.MonoChar (AlgebraicClosure ℚ),
        ∀ x, ψ'.1 x = HahnSeries.hahnTwist χ (ψ.1 x) := by sorry
