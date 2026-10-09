module

public import Definitions.FLT.Def_EllipticCurve_PointReduction

import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_reducePoint_some

set_option autoImplicit false

open WeierstrassCurve IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum

namespace ReduceSome

theorem reducePoint_some' (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (W : WeierstrassCurve K) [W.HasGoodReduction R] {x y : K} (h : W.toAffine.Nonsingular x y)
    (hx : valuation K (IsDiscreteValuationRing.maximalIdeal R) x ≤ 1) (hy : valuation K (IsDiscreteValuationRing.maximalIdeal R) y ≤ 1) :
    ∃ h', reducePoint_alt R W (.some x y h) = .some (reduceCoord R x) (reduceCoord R y) h' := by
  obtain ⟨rx, hrx⟩ := exists_lift_of_le_one hx
  obtain ⟨ry, hry⟩ := exists_lift_of_le_one hy
  have hex : ∃ r : R, algebraMap R K r = x := ⟨rx, hrx⟩
  have hey : ∃ r : R, algebraMap R K r = y := ⟨ry, hry⟩

  have hcx : reduceCoord R x = residue R rx := by
    rw [reduceCoord, dite_eq_left hex]
    exact congrArg _ (IsFractionRing.injective R K (hex.choose_spec.trans hrx.symm))
  have hcy : reduceCoord R y = residue R ry := by
    rw [reduceCoord, dite_eq_left hey]
    exact congrArg _ (IsFractionRing.injective R K (hey.choose_spec.trans hry.symm))

  have heqK : ((integralModel R W).map (algebraMap R K)).toAffine.Equation
      (algebraMap R K rx) (algebraMap R K ry) := by
    have hbc : (integralModel R W).map (algebraMap R K) = W := baseChange_integralModel_eq R W
    rw [hbc, hrx, hry]
    exact h.1
  have heqR : (integralModel R W).toAffine.Equation rx ry :=
    (Affine.map_equation _ (IsFractionRing.injective R K) _ _).mp heqK

  have heqk : (reduction R W).toAffine.Equation (residue R rx) (residue R ry) :=
    heqR.map (residue R)

  have hell : (reduction R W).IsElliptic :=
    (hasGoodReduction_iff_isElliptic_reduction R).mp ‹W.HasGoodReduction R›
  have hns : (reduction R W).toAffine.Nonsingular (reduceCoord R x) (reduceCoord R y) := by
    rw [hcx, hcy]
    exact Affine.equation_iff_nonsingular.mp heqk
  have hxy : valuation K (IsDiscreteValuationRing.maximalIdeal R) x ≤ 1 ∧ valuation K (IsDiscreteValuationRing.maximalIdeal R) y ≤ 1 := ⟨hx, hy⟩
  refine ⟨hns, ?_⟩
  simp only [reducePoint_alt, dite_eq_left hxy, dite_eq_left hns]

end ReduceSome

theorem solution
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) [W.HasGoodReduction R] {x y : K} (h : W.toAffine.Nonsingular x y)
    (hx : IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) x ≤ 1)
    (hy : IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) y ≤ 1) :
    ∃ h', WeierstrassCurve.reducePoint_alt R W (.some x y h)
      = .some (WeierstrassCurve.reduceCoord R x) (WeierstrassCurve.reduceCoord R y) h' :=
  ReduceSome.reducePoint_some' R W h hx hy

end S_WeierstrassCurve_reducePoint_some
end P2MW
export P2MW.S_WeierstrassCurve_reducePoint_some (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem WeierstrassCurve.reducePoint_some
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) [W.HasGoodReduction R] {x y : K} (h : W.toAffine.Nonsingular x y)
    (hx : IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) x ≤ 1)
    (hy : IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) y ≤ 1) :
    ∃ h', WeierstrassCurve.reducePoint_alt R W (.some x y h)
      = .some (WeierstrassCurve.reduceCoord R x) (WeierstrassCurve.reduceCoord R y) h' := _root_.P2MW.S_WeierstrassCurve_reducePoint_some.solution R W h hx hy

end publicSection
