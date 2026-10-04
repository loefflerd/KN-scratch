module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_evalEval_psi_sq

open Polynomial
open scoped Polynomial.Bivariate

theorem PortCard.evalEval_ψ_sq {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}
    (h : W.toAffine.Equation x y) (n : ℤ) : (W.ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x := by
  have hmk : WeierstrassCurve.Affine.CoordinateRing.mk W (W.ψ n ^ 2) =
      WeierstrassCurve.Affine.CoordinateRing.mk W (C (W.ΨSq n)) := by
    rw [map_pow, WeierstrassCurve.Affine.CoordinateRing.mk_ψ,
      WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq]
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_eq_mk.mp hmk
  have h0 : (W.toAffine.polynomial).evalEval x y = 0 := h
  have h1 := congrArg (evalEval x y) hp
  rw [evalEval_sub, evalEval_mul, h0, zero_mul, sub_eq_zero, evalEval_pow, evalEval_C] at h1
  exact h1

theorem PortCard.evalEval_φ {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}
    (h : W.toAffine.Equation x y) (n : ℤ) : (W.φ n).evalEval x y = (W.Φ n).eval x := by
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_eq_mk.mp (WeierstrassCurve.Affine.CoordinateRing.mk_φ W n)
  have h0 : (W.toAffine.polynomial).evalEval x y = 0 := h
  have h1 := congrArg (evalEval x y) hp
  rw [evalEval_sub, evalEval_mul, h0, zero_mul, sub_eq_zero, evalEval_C] at h1
  exact h1

theorem solution {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R} (h : W.toAffine.Equation x y) (n : ℤ) : (W.ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x :=
  PortCard.evalEval_ψ_sq W h n

end S_WeierstrassCurve_Affine_evalEval_psi_sq
end P2MW
export P2MW.S_WeierstrassCurve_Affine_evalEval_psi_sq (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem WeierstrassCurve.Affine.evalEval_psi_sq {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R} (h : W.toAffine.Equation x y) (n : ℤ) : (W.ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x := _root_.P2MW.S_WeierstrassCurve_Affine_evalEval_psi_sq.solution W h n

end publicSection
