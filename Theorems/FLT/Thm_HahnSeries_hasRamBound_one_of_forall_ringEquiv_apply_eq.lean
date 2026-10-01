import Mathlib.FieldTheory.IsAlgClosed.Basic

import Definitions.FLT.Def_HahnSeries_RamificationBound

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem HahnSeries.hasRamBound_one_of_forall_ringEquiv_apply_eq
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] {x : HahnSeries ℚ K}
    (hx : ∀ σ : HahnSeries ℚ K ≃+* HahnSeries ℚ K,
      (∀ z : HahnSeries ℚ K, (σ z).orderTop = z.orderTop) →
      (∀ z : HahnSeries ℚ K, HahnSeries.HasRamBound 1 z → σ z = z) → σ x = x) :
    HahnSeries.HasRamBound 1 x := by sorry
