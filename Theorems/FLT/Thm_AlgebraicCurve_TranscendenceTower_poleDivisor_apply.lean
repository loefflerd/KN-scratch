import Definitions.FLT.Def_AlgebraicCurve_PoleDivisorPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve
theorem TranscendenceTower.poleDivisor_apply {K : Type*} {E : Type*} {F : Type*} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] (T : TranscendenceTower K E F) (w : Place K F) :
    T.poleDivisor w = (w.ramificationIndex E : ℤ) * (Finsupp.single T.v 1) (w.restrict E) := by sorry
