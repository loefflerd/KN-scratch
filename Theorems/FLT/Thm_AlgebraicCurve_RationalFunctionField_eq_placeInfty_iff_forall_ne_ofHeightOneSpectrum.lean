import Definitions.FLT.Def_AlgebraicCurve_RatFuncPlaceInfty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve AlgebraicCurve.RationalFunctionField
theorem AlgebraicCurve.RationalFunctionField.eq_placeInfty_iff_forall_ne_ofHeightOneSpectrum {K : Type*} [Field K] [DecidableEq (RatFunc K)] (v : Place K (RatFunc K)) : v = placeInfty K ↔ ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K), v ≠ Place.ofHeightOneSpectrum w := by sorry
