import Definitions.FLT.Def_AlgebraicCurve_RatFuncPlaceInfty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve AlgebraicCurve.RationalFunctionField
theorem P2M.Dup.AlgebraicCurve.RationalFunctionField.eq_ofHeightOneSpectrum_or_eq_placeInfty {K : Type*} [Field K] [DecidableEq (RatFunc K)] (v : Place K (RatFunc K)) : (∃ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K), v = Place.ofHeightOneSpectrum w) ∨ v = placeInfty K := by sorry
