module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsAddCyclic_of_squarefree_natCard

theorem solution
    {A : Type*} [AddCommGroup A] (hA : Squarefree (Nat.card A)) : IsAddCyclic A := by
  have : Finite A := Nat.finite_of_card_ne_zero hA.ne_zero
  rw [← isCyclic_multiplicative_iff]
  have hM : Squarefree (Nat.card (Multiplicative A)) := by
    rwa [Nat.card_congr Multiplicative.toAdd]
  have : IsZGroup (Multiplicative A) := IsZGroup.of_squarefree hM
  exact IsCyclic.of_exponent_eq_card (IsZGroup.exponent_eq_card (Multiplicative A))

end S_IsAddCyclic_of_squarefree_natCard
end P2MW
export P2MW.S_IsAddCyclic_of_squarefree_natCard (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem IsAddCyclic.of_squarefree_natCard
    {A : Type*} [AddCommGroup A] (hA : Squarefree (Nat.card A)) : IsAddCyclic A := _root_.P2MW.S_IsAddCyclic_of_squarefree_natCard.solution hA

end publicSection
