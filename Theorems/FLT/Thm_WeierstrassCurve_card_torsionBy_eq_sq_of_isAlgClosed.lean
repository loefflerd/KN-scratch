module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import Theorems.FLT.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed_light
import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_card_torsionBy_eq_sq_of_isAlgClosed
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

open WeierstrassCurve

theorem solution {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
    (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hn : (n : F) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ W.toAffine.Point n) = n ^ 2 :=
  WeierstrassCurve.card_torsion_of_isAlgClosed_light (F := F) (K := F) W hn

end S_WeierstrassCurve_card_torsionBy_eq_sq_of_isAlgClosed
end P2MW
export P2MW.S_WeierstrassCurve_card_torsionBy_eq_sq_of_isAlgClosed (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
    (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hn : (n : F) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ W.toAffine.Point n) = n ^ 2 := _root_.P2MW.S_WeierstrassCurve_card_torsionBy_eq_sq_of_isAlgClosed.solution W hn

end publicSection
