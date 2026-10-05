import Definitions.FLT.Def_AlgebraicCurve_RiemannRochRows

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve KaehlerDifferential
theorem AlgebraicCurve.ell_canonicalDivisor_eq_genus_of_riemannRoch {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates] (hRR : FunctionFieldRiemannRoch K F) (hC : ConstantsAreBase K F) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    (ell (canonicalDivisorOf hω) : ℤ) = (genus K F : ℤ) := by sorry
