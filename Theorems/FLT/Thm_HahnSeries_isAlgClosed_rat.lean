import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.HahnSeries.Summable

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem HahnSeries.isAlgClosed_rat {K : Type*} [Field K] [IsAlgClosed K] :
    IsAlgClosed (HahnSeries ℚ K) := by sorry
