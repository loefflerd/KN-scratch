import Mathlib.RingTheory.HahnSeries.PowerSeries

import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.FLT.Def_HahnSeries_RamificationBound

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem AlgebraicCurve.Place.exists_ord_mul_eq_order_of_hasRamBound
    {K L F : Type*} [Field K] [Field L] [Algebra K L] [Field F] [Algebra K F]
    (φ : F →ₐ[K] HahnSeries ℚ L) {d : ℕ} (hd : 0 < d)
    (hφ : ∀ x : F, HahnSeries.HasRamBound d (φ x))
    (hnt : ∃ x : F, (φ x).order ≠ 0) :
    ∃ (w : AlgebraicCurve.Place K F) (g : ℚ), 0 < g ∧
      ∀ x : F, (w.ord x : ℚ) * g = (φ x).order := by sorry
