module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FieldSimp
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
import Definitions.FLT.Def_WeierstrassCurve_EDSEngine
import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff

theorem solution {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    {x y : F} (h : W.toAffine.Nonsingular x y) (n : ℤ) :
    n • (WeierstrassCurve.Affine.Point.some x y h) = 0 ↔ (W.ψ n).evalEval x y = 0 :=
  W.smul_eq_zero_iff_evalEval_ψ h n

end S_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
end P2MW
export P2MW.S_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    {x y : F} (h : W.toAffine.Nonsingular x y) (n : ℤ) :
    n • (WeierstrassCurve.Affine.Point.some x y h) = 0 ↔ (W.ψ n).evalEval x y = 0 := _root_.P2MW.S_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff.solution W h n

end publicSection
