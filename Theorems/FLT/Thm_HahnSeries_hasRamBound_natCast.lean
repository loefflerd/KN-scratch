import Definitions.FLT.Def_HahnSeries_RamificationBound

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open HahnSeries
theorem HahnSeries.hasRamBound_natCast {K : Type*} [Field K] {e : ℕ} (n : ℕ) : HasRamBound e ((n : HahnSeries ℚ K)) := by sorry
