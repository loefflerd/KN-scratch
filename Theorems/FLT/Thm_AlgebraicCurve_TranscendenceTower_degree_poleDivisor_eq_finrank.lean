import Definitions.FLT.Def_AlgebraicCurve_PoleDivisorPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve
theorem TranscendenceTower.degree_poleDivisor_eq_finrank {K : Type*} {E : Type*} {F : Type*} [Field K] [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F] [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] (T : TranscendenceTower K E F) :
    Divisor.degree T.poleDivisor = (Module.finrank E F : ℤ) := by sorry
