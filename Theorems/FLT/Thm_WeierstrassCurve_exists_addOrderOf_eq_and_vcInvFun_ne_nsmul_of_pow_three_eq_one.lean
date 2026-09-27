import Mathlib
import Definitions.FLT.Def_WeierstrassCurve_VariableChangePointEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem WeierstrassCurve.exists_addOrderOf_eq_and_vcInvFun_ne_nsmul_of_pow_three_eq_one
    {L : Type*} [Field L] [DecidableEq L] [Algebra ℚ L] [IsAlgClosed L]
    (B : L) (hB : B ≠ 0) (u : Lˣ) (hu : (u : L) ^ 3 = 1) (hu1 : (u : L) ≠ 1)
    (p : ℕ) (hp : p.Prime) :
    ∃ T : (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve L).toAffine.Point, addOrderOf T = p ∧
      ∀ k : ℕ, ¬ HEq (WeierstrassCurve.Affine.Point.vcInvFun (⟨u, 0, 0, 0⟩ : WeierstrassCurve.VariableChange L)
        (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve L).toAffine T) (k • T) := by sorry
