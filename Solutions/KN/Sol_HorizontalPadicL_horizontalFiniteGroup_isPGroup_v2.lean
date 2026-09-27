import Definitions.KN.Def_KN_SeededThetaConstructionV2B
import Mathlib.GroupTheory.PGroup

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HorizontalPadicL

/-- Every finite horizontal quotient is a finite `p`-group. -/
theorem _root_.solution
    {p : ℕ} [Fact p.Prime] (m : ℕ → ℕ) (A : Finset ℕ) :
    IsPGroup p (HorizontalFiniteGroup p m A) := by
  rw [IsPGroup.iff_card]
  refine ⟨∑ i : {n : ℕ // n ∈ A}, m i.1, ?_⟩
  simp [HorizontalFiniteGroup, ← Finset.prod_pow_eq_pow_sum]

end HorizontalPadicL
