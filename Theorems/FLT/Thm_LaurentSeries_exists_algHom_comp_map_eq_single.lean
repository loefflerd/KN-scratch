import Mathlib.RingTheory.LaurentSeries
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open HahnSeries
theorem LaurentSeries.exists_algHom_comp_map_eq_single {K F : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    [Field F] [Algebra K F] (φ : F →ₐ[K] LaurentSeries K) (f : F) (hf : 0 < (φ f).order) :
    ∃ φ' : F →ₐ[K] LaurentSeries K,
      (∀ x : F, (φ' x).order = (φ x).order) ∧ φ' f = single (φ f).order 1 := by sorry
