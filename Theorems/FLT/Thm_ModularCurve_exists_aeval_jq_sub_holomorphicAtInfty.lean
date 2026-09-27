import Definitions.FLT.Def_ModularCurve_X0
import Definitions.FLT.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.exists_aeval_jq_sub_holomorphicAtInfty (n : ℕ) : ∀ f : LaurentSeries ℚ, PoleOrderLE f n → ∃ P : Polynomial ℚ, P.natDegree ≤ n ∧ PoleOrderLE (f - Polynomial.aeval jq P) 0 := by sorry
