import Definitions.FLT.Def_ModularCurve_X0
import Definitions.FLT.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.mem_range_coeffEmb_qExpand_of_mem_inter {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {f : LaurentSeries K} (h1 : f ∈ Set.range (ModularCurve.qExpand K ℓ)) (h2 : f ∈ Set.range (coeffEmb K)) : ∃ g : LaurentSeries ℚ, f = coeffEmb K (ModularCurve.qExpand ℚ ℓ g) := by sorry
