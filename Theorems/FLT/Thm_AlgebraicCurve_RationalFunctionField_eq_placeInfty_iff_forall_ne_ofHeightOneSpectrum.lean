module

public import Definitions.FLT.Def_AlgebraicCurve_RatFuncPlaceInfty

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.FLT.Def_AlgebraicCurve_RatFuncPlaceClassification
import Theorems.FLT.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_placeInfty_ne_ofHeightOneSpectrum
import Theorems.FLT.Thm_AlgebraicCurve_RationalFunctionField_subsingleton_setOf_forall_ne_ofHeightOneSpectrum
import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_eq_placeInfty_iff_forall_ne_ofHeightOneSpectrum
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

open IsDedekindDomain AlgebraicCurve AlgebraicCurve.RationalFunctionField

theorem solution {K : Type*} [Field K] [DecidableEq (RatFunc K)] (v : Place K (RatFunc K)) : v = placeInfty K ↔ ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K), v ≠ Place.ofHeightOneSpectrum w := by
  constructor
  · rintro rfl
    exact AlgebraicCurve.RationalFunctionField.placeInfty_ne_ofHeightOneSpectrum K
  · intro h
    exact AlgebraicCurve.RationalFunctionField.subsingleton_setOf_forall_ne_ofHeightOneSpectrum h
      (AlgebraicCurve.RationalFunctionField.placeInfty_ne_ofHeightOneSpectrum K)

end S_AlgebraicCurve_RationalFunctionField_eq_placeInfty_iff_forall_ne_ofHeightOneSpectrum
end P2MW
export P2MW.S_AlgebraicCurve_RationalFunctionField_eq_placeInfty_iff_forall_ne_ofHeightOneSpectrum (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve AlgebraicCurve.RationalFunctionField
theorem AlgebraicCurve.RationalFunctionField.eq_placeInfty_iff_forall_ne_ofHeightOneSpectrum {K : Type*} [Field K] [DecidableEq (RatFunc K)] (v : Place K (RatFunc K)) : v = placeInfty K ↔ ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K), v ≠ Place.ofHeightOneSpectrum w := _root_.P2MW.S_AlgebraicCurve_RationalFunctionField_eq_placeInfty_iff_forall_ne_ofHeightOneSpectrum.solution v

end publicSection
