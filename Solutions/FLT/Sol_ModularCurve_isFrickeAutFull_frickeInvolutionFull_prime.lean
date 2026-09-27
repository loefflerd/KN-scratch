import Definitions.FLT.Def_ModularCurve_AtkinLehner
import Theorems.FLT.Thm_ModularCurve_exists_isFrickeAutFull
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open ModularCurve AlgebraicCurve IntermediateField

noncomputable section

theorem solution (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] : IsFrickeAutFull ℓ (frickeInvolutionFull ℓ) := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  exact ModularCurve.isFrickeAutFull_frickeInvolutionFull ℓ (ModularCurve.exists_isFrickeAutFull ℓ)

end

end S_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime
end P2MW
export P2MW.S_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime (solution)
