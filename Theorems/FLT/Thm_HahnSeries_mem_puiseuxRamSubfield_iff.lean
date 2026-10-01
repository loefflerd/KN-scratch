import Definitions.FLT.Def_HahnSeries_RamificationBound

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem HahnSeries.mem_puiseuxRamSubfield_iff {K : Type*} [Field K] {e : ℕ} (he : 0 < e)
    {y : HahnSeries ℚ K} :
    y ∈ HahnSeries.puiseuxRamSubfield K he ↔ HahnSeries.HasRamBound e y := by sorry
