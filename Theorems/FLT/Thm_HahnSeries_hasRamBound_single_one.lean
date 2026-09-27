import Definitions.FLT.Def_HahnSeries_RamificationBound

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open HahnSeries
theorem HahnSeries.hasRamBound_single_one {K : Type*} [Field K] {e : ℕ} (he : 0 < e) (c : K) :
    HasRamBound e (single (1 : ℚ) c) := by sorry
