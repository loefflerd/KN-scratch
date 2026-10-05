module

public import Definitions.FLT.Def_AlgebraicCurve_RiemannRochRows

import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_ell_canonicalDivisor_eq_genus_of_riemannRoch

open AlgebraicCurve KaehlerDifferential

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates] (hRR : FunctionFieldRiemannRoch K F) (hC : ConstantsAreBase K F) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    (ell (canonicalDivisorOf hω) : ℤ) = (genus K F : ℤ) := by
  have h0 := hRR hω 0
  rw [map_zero, ell_zero_eq_one_of_constantsAreBase hC, sub_zero] at h0
  push_cast at h0
  linarith

end S_AlgebraicCurve_ell_canonicalDivisor_eq_genus_of_riemannRoch
end P2MW
export P2MW.S_AlgebraicCurve_ell_canonicalDivisor_eq_genus_of_riemannRoch (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve KaehlerDifferential
theorem AlgebraicCurve.ell_canonicalDivisor_eq_genus_of_riemannRoch {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates] (hRR : FunctionFieldRiemannRoch K F) (hC : ConstantsAreBase K F) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    (ell (canonicalDivisorOf hω) : ℤ) = (genus K F : ℤ) := _root_.P2MW.S_AlgebraicCurve_ell_canonicalDivisor_eq_genus_of_riemannRoch.solution hRR hC hω

end publicSection
