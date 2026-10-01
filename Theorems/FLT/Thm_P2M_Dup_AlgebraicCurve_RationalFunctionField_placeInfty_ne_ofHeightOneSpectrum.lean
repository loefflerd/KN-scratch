import Definitions.FLT.Def_AlgebraicCurve_RatFuncPlaceInfty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve AlgebraicCurve.RationalFunctionField
theorem P2M.Dup.AlgebraicCurve.RationalFunctionField.placeInfty_ne_ofHeightOneSpectrum (K : Type*) [Field K] [DecidableEq (RatFunc K)] (w : IsDedekindDomain.HeightOneSpectrum (Polynomial K)) : placeInfty K ≠ Place.ofHeightOneSpectrum w := by sorry
