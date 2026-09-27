import Mathlib
import Definitions.FLT.Def_AlgebraicCurve_Repartitions
import Definitions.FLT.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
theorem AlgebraicCurve.exists_divisor_forall_eq_weightFloor
    (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] [AlgebraicCurve.IsCurveOver K F]
    (y : F) (m : ℕ) :
    ∃ D : AlgebraicCurve.Divisor K F, ∀ w : AlgebraicCurve.Place K F,
      D w = (if 0 < w.ord y then (2 * (m : ℤ) * w.ord y) / 3 else 0)
          + (if 0 < w.ord (y - 1728) then ((m : ℤ) * w.ord (y - 1728)) / 2 else 0)
          + (if w.ord y < 0 then (m : ℤ) * w.ord y else 0) := by sorry
