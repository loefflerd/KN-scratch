import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

import Definitions.FLT.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem ZMod.natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi (n : ℕ) [NeZero n] :
    Nat.card {H : AddSubgroup (ZMod n × ZMod n) // IsAddCyclic H ∧ Nat.card H = n} = ModularCurve.dedekindPsi n := by sorry
