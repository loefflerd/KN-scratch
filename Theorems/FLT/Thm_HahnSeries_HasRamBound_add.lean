import Definitions.FLT.Def_HahnSeries_RamificationBound

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open HahnSeries
theorem HahnSeries.HasRamBound.add {K : Type*} [Field K] {e : ℕ} {x y : HahnSeries ℚ K} (hx : HasRamBound e x)
    (hy : HasRamBound e y) : HasRamBound e (x + y) := by sorry
