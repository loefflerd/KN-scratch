import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem Nat.exists_squarefree_sq_add (D : ℕ) (hD : 1 ≤ D) :
    ∃ c : ℕ, 1 ≤ c ∧ Squarefree (c ^ 2 + D) := by sorry
