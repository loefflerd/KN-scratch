import Mathlib
import Definitions.FLT.Def_ModularCurve_X0
import Theorems.FLT.Thm_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

theorem solution
    (N : ℕ) [NeZero N] (h2 : 2 ≤ N) (hN : ¬ IsSquare N) (data : ModularCurve.ModularPolynomialData N) :
    IsUnit (data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X).leadingCoeff :=
  (fun _ => ModularCurve.ModularPolynomialData.isUnit_leadingCoeff_diag_of_not_isSquare N hN data) h2


end S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag (solution)
