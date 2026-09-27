import Definitions.KN.Def_KN_SeededThetaConstructionV2B
import Mathlib.GroupTheory.PGroup

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HorizontalPadicL

/-- Every finite horizontal quotient is a finite `p`-group. -/
theorem horizontalFiniteGroup_isPGroup_v2
    {p : ℕ} [Fact p.Prime] (m : ℕ → ℕ) (A : Finset ℕ) :
    IsPGroup p (HorizontalFiniteGroup p m A) := by sorry

end HorizontalPadicL
