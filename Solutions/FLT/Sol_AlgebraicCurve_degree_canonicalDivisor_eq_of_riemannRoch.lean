import Definitions.FLT.Def_AlgebraicCurve_RiemannRochRows

open AlgebraicCurve KaehlerDifferential

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates] (hRR : FunctionFieldRiemannRoch K F) (hC : ConstantsAreBase K F) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    Divisor.degree (canonicalDivisorOf hω) = 2 * (genus K F : ℤ) - 2 := by
  have h0 := hRR hω 0
  rw [map_zero, ell_zero_eq_one_of_constantsAreBase hC, sub_zero] at h0
  push_cast at h0
  have hW := hRR hω (canonicalDivisorOf hω)
  rw [sub_self, ell_zero_eq_one_of_constantsAreBase hC] at hW
  push_cast at hW
  linarith
