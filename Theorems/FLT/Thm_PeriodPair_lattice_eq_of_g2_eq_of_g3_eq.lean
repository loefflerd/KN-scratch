import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem PeriodPair.lattice_eq_of_g2_eq_of_g3_eq (L L' : PeriodPair)
    (h₂ : L.g₂ = L'.g₂) (h₃ : L.g₃ = L'.g₃) : L.lattice = L'.lattice := by sorry
