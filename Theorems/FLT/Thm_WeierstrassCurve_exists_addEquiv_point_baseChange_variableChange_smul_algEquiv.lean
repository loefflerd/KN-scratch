module

public import Definitions.FLT.Def_FLTPrelim_GaloisRep
public import Definitions.FLT.Def_P2M_Util

import Theorems.FLT.Thm_WeierstrassCurve_exists_addEquiv_point_of_variableChange_eq

section privateSection

namespace P2MW.S_WeierstrassCurve_exists_addEquiv_point_baseChange_variableChange_smul_algEquiv

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
    (W : WeierstrassCurve F) (γ : WeierstrassCurve.VariableChange F) :
    ∃ φ : ((γ • W).baseChange K).toAffine.Point ≃+ (W.baseChange K).toAffine.Point,
      ∀ (σ : K ≃ₐ[F] K) (P : ((γ • W).baseChange K).toAffine.Point), φ (σ • P) = σ • φ P :=
  WeierstrassCurve.exists_addEquiv_point_of_variableChange_eq K γ⁻¹ (inv_smul_smul γ W)
end S_WeierstrassCurve_exists_addEquiv_point_baseChange_variableChange_smul_algEquiv
end P2MW

end privateSection

public section publicSection

theorem WeierstrassCurve.exists_addEquiv_point_baseChange_variableChange_smul_algEquiv {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] (W : WeierstrassCurve F) (γ : WeierstrassCurve.VariableChange F) : ∃ φ : ((γ • W).baseChange K).toAffine.Point ≃+ (W.baseChange K).toAffine.Point, ∀ (σ : K ≃ₐ[F] K) (P : ((γ • W).baseChange K).toAffine.Point), φ (σ • P) = σ • φ P := _root_.P2MW.S_WeierstrassCurve_exists_addEquiv_point_baseChange_variableChange_smul_algEquiv.solution W γ

end publicSection
