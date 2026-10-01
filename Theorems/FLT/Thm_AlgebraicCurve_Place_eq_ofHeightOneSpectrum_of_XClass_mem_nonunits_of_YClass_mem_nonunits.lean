import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.SimpleRing.Principal

import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine

universe u
theorem AlgebraicCurve.Place.eq_ofHeightOneSpectrum_of_XClass_mem_nonunits_of_YClass_mem_nonunits
    {F : Type u} [Field F] {W : WeierstrassCurve.Affine F} [IsDedekindDomain W.CoordinateRing]
    {x y : F} (v : AlgebraicCurve.Place F W.FunctionField)
    (hX : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.XClass W x)
      ∈ v.toValuationSubring.nonunits)
    (hY : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.YClass W (Polynomial.C y))
      ∈ v.toValuationSubring.nonunits)
    (w : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing)
    (hw : w.asIdeal = CoordinateRing.XYIdeal W x (Polynomial.C y)) :
    v = Place.ofHeightOneSpectrum (K := F) w := by sorry
