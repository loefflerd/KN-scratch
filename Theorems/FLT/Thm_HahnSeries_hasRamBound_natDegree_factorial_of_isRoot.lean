import Mathlib
import Definitions.FLT.Def_HahnSeries_RamificationBound

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem HahnSeries.hasRamBound_natDegree_factorial_of_isRoot
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {p : Polynomial (HahnSeries ℚ K)} (hp : p ≠ 0)
    (hcoeff : ∀ i : ℕ, HahnSeries.HasRamBound 1 (p.coeff i))
    {y : HahnSeries ℚ K} (hy : p.IsRoot y) :
    HahnSeries.HasRamBound p.natDegree.factorial y := by sorry
