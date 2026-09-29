import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Countable.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u
theorem Field.nonempty_ringHom_complex_of_countable
    (K : Type u) [Field K] [CharZero K] [Countable K] : Nonempty (K →+* ℂ) := by sorry
