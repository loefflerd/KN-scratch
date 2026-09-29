import Mathlib.Algebra.Squarefree.Basic
import Mathlib.SetTheory.Cardinal.Finite

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem IsAddCyclic.of_squarefree_natCard
    {A : Type*} [AddCommGroup A] (hA : Squarefree (Nat.card A)) : IsAddCyclic A := by sorry
