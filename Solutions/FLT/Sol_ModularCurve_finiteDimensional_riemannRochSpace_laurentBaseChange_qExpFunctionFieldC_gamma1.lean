import Theorems.FLT.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.FLT.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.FLT.Thm_AlgebraicCurve_finiteDimensional_lSpace_zero
import Theorems.FLT.Thm_AlgebraicCurve_nonempty_place_of_transcendental_of_finiteDimensional
import Theorems.FLT.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.FLT.Thm_ModularCurve_isCurveOver_laurentBaseChange_qExpFunctionFieldC_gamma1
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finiteDimensional_riemannRochSpace_laurentBaseChange_qExpFunctionFieldC_gamma1
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option synthInstance.maxHeartbeats 1600000

open ModularCurve CongruenceSubgroup AlgebraicCurve
open scoped MatrixGroups

set_option maxHeartbeats 6400000 in
theorem solution
    (K : Type*) [Field K] [Algebra ℚ K] [IsAlgClosed K] (M : ℕ) [NeZero M]
    (D : AlgebraicCurve.Divisor K ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)))) :
    FiniteDimensional K ↥(AlgebraicCurve.riemannRochSpace D) := by
  obtain ⟨x, htr, hfd⟩ : ∃ x : ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))),
      Transcendental K x ∧ FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set _)) _ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
      K (CongruenceSubgroup.Gamma1 M) (by rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T])
  have := hfd
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have : Algebra.IsAlgebraic ↥(IntermediateField.adjoin K ({x} : Set _))
      ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))) :=
    Algebra.IsAlgebraic.of_finite _ _
  have : Algebra.IsSeparable ↥(IntermediateField.adjoin K ({x} : Set _))
      ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have := AlgebraicCurve.nonempty_place_of_transcendental_of_finiteDimensional K x htr hfd
  have := ModularCurve.isCurveOver_laurentBaseChange_qExpFunctionFieldC_gamma1 K M
  have := AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional htr hfd
  have := AlgebraicCurve.finiteDimensional_lSpace_zero K
    ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)))
  exact AlgebraicCurve.finiteDimensional_lSpace D

end S_ModularCurve_finiteDimensional_riemannRochSpace_laurentBaseChange_qExpFunctionFieldC_gamma1
end P2MW
export P2MW.S_ModularCurve_finiteDimensional_riemannRochSpace_laurentBaseChange_qExpFunctionFieldC_gamma1 (solution)
