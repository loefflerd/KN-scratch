import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

import Definitions.FLT.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem AddCommGroup.natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy
    (n : ℕ) [NeZero n] {A : Type*} [AddCommGroup A]
    (e : ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n) :
    Nat.card {H : AddSubgroup A // IsAddCyclic H ∧ Nat.card H = n} = ModularCurve.dedekindPsi n := by sorry
