module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_ne_bot

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate

theorem solution {R : Type*} [CommRing R] [Nontrivial R] {W : Affine R} (x : R) (y : R[X]) : XYIdeal W x y ≠ ⊥ := fun h0 =>
  XClass_ne_zero (W' := W) x <| by
    have : XClass W x ∈ XYIdeal W x y := Ideal.subset_span (by simp)
    rwa [h0, Ideal.mem_bot] at this

end S_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_ne_bot
end P2MW
export P2MW.S_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_ne_bot (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate
theorem WeierstrassCurve.Affine.CoordinateRing.XYIdeal_ne_bot {R : Type*} [CommRing R] [Nontrivial R] {W : Affine R} (x : R) (y : R[X]) : XYIdeal W x y ≠ ⊥ := _root_.P2MW.S_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_ne_bot.solution x y

end publicSection
