import Mathlib.Data.Nat.Prime.Defs
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.SetTheory.Cardinal.Finite

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem MulAction.card_mul_natCard_orbitRel_quotient_eq_of_natCard_eq_prime
    (G : Type*) {X : Type*} [Group G] [MulAction G X] [Finite G] [Finite X]
    {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p) :
    p * Nat.card (MulAction.orbitRel.Quotient G X)
      = Nat.card X + (p - 1) * Nat.card (MulAction.fixedPoints G X) := by sorry
