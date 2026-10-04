module

public import Definitions.FLT.Def_ModularCurve_QExpansionDiff
public import Definitions.FLT.Def_ModularCurve_LaurentCoeff

import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_thetaL_coeffMap_eq_coeffMap_single_mul_derivative

namespace ModularCurve
p2m_export "ModularCurve" "thetaL thetaL_apply coeffMap coeffMap_coeff"
p2m_open "ModularCurve"

section

variable {R K : Type*} [CommRing R] [Field K]

private theorem coeffMap_single_one (φ : R →+* K) :
    coeffMap φ (HahnSeries.single (1 : ℤ) (1 : R)) = HahnSeries.single (1 : ℤ) (1 : K) := by
  ext n
  rw [coeffMap_coeff, HahnSeries.coeff_single, HahnSeries.coeff_single]
  split_ifs <;> simp

private theorem derivative_coeffMap (φ : R →+* K) (w : LaurentSeries R) :
    LaurentSeries.derivative K (coeffMap φ w) = coeffMap φ (LaurentSeries.derivative R w) := by
  ext n
  rw [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff, coeffMap_coeff,
    coeffMap_coeff, LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff, map_zsmul]

private theorem thetaL_coeffMap_impl (φ : R →+* K) (w : LaurentSeries R) :
    thetaL K (coeffMap φ w) =
      coeffMap φ (HahnSeries.single (1 : ℤ) (1 : R) * LaurentSeries.derivative R w) := by
  rw [thetaL_apply, derivative_coeffMap, map_mul, coeffMap_single_one]

end

end ModularCurve

theorem solution {R : Type*} [CommRing R]
    {K : Type*} [Field K] (φ : R →+* K) (w : LaurentSeries R) :
    ModularCurve.thetaL K (ModularCurve.coeffMap φ w) =
      ModularCurve.coeffMap φ (HahnSeries.single (1 : ℤ) (1 : R) * LaurentSeries.derivative R w) :=
  ModularCurve.thetaL_coeffMap_impl φ w

end S_ModularCurve_thetaL_coeffMap_eq_coeffMap_single_mul_derivative
end P2MW
export P2MW.S_ModularCurve_thetaL_coeffMap_eq_coeffMap_single_mul_derivative (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.thetaL_coeffMap_eq_coeffMap_single_mul_derivative {R : Type*} [CommRing R]
    {K : Type*} [Field K] (φ : R →+* K) (w : LaurentSeries R) :
    ModularCurve.thetaL K (ModularCurve.coeffMap φ w) =
      ModularCurve.coeffMap φ (HahnSeries.single (1 : ℤ) (1 : R) * LaurentSeries.derivative R w) := _root_.P2MW.S_ModularCurve_thetaL_coeffMap_eq_coeffMap_single_mul_derivative.solution φ w

end publicSection
