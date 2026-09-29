import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem WeierstrassCurve.variableChange_mk_smul_eq_self_of_sq_eq_neg_one
    {R : Type*} [CommRing R] (u : Rˣ) (hu : (u : R) ^ 2 = -1) (A : R) :
    (⟨u, 0, 0, 0⟩ : WeierstrassCurve.VariableChange R) • (⟨0, 0, 0, A, 0⟩ : WeierstrassCurve R) =
      ⟨0, 0, 0, A, 0⟩ := by sorry
