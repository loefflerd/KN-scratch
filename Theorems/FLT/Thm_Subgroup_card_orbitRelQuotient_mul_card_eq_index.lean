import Mathlib.GroupTheory.Index

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
theorem Subgroup.card_orbitRelQuotient_mul_card_eq_index {M : Type*} [Group M] (H K : Subgroup M)
    (hKH : ∀ g x : M, x ∈ K → g⁻¹ * x * g ∈ H → x = 1) :
    Nat.card (MulAction.orbitRel.Quotient H (M ⧸ K)) * Nat.card K = H.index := by sorry
