import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem WeierstrassCurve.variableChange_smul_eq_self_iff_of_c4_ne_zero_of_c6_ne_zero
    {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (E : WeierstrassCurve F)
    (hc₄ : E.c₄ ≠ 0) (hc₆ : E.c₆ ≠ 0) (C : WeierstrassCurve.VariableChange F) :
    C • E = E ↔ C = 1 ∨ C = ⟨-1, 0, -E.a₁, -E.a₃⟩ := by sorry
