import Definitions.FLT.Def_ModularCurve_EMD
import Definitions.FLT.Def_HahnSeries_Monodromy

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open HahnSeries ModularCurve AlgebraicCurve
theorem ModularCurve.samePlace_iff_exists_monodromy (N : ℕ) [NeZero N] (j₀ : AlgebraicClosure ℚ)
    (ψ ψ' : Emb N j₀) :
    SamePlace ψ.1 ψ'.1 ↔
      ∃ m ∈ monodromy (AlgebraicClosure ℚ),
        (↑m : HahnSeries ℚ (AlgebraicClosure ℚ) →ₐ[AlgebraicClosure ℚ]
          HahnSeries ℚ (AlgebraicClosure ℚ)).comp ψ.1 = ψ'.1 := by sorry
