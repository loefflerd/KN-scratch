module

public import Definitions.KN.Def_KN_SeededThetaConstructionV2B
public import Mathlib.GroupTheory.PGroup

public noncomputable section publicSection

open scoped BigOperators

/-- Every finite horizontal quotient is a finite `p`-group. -/
theorem HorizontalPadicL.horizontalFiniteGroup_isPGroup_v2
    {p : ℕ} [Fact p.Prime] (m : ℕ → ℕ) (A : Finset ℕ) :
    IsPGroup p (HorizontalFiniteGroup p m A) := by
  rw [IsPGroup.iff_card]
  refine ⟨∑ i : {n : ℕ // n ∈ A}, m i.1, ?_⟩
  simp [HorizontalFiniteGroup, ← Finset.prod_pow_eq_pow_sum]

end publicSection
