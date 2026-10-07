module

public import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PicardGroup
import Theorems.FLT.Thm_AlgebraicCurve_RationalFunctionField_nonempty_place_of_ratFunc_tower
import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_nonempty_place_of_transcendental_of_finiteDimensional
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

theorem solution
    (k : Type*) [Field k] {F : Type*} [Field F] [Algebra k F] (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional ↥(IntermediateField.adjoin k ({x} : Set F)) F)
    [Algebra.IsSeparable ↥(IntermediateField.adjoin k ({x} : Set F)) F] :
    Nonempty (AlgebraicCurve.Place k F) := by
  classical
  set E := IntermediateField.adjoin k ({x} : Set F) with hE
  have : FiniteDimensional ↥E F := hfin
  let e : RatFunc k ≃ₐ[k] ↥E := RatFunc.algEquivOfTranscendental x hx
  let algRE : Algebra (RatFunc k) ↥E := e.toAlgHom.toRingHom.toAlgebra
  let algRF : Algebra (RatFunc k) F := ((algebraMap ↥E F).comp e.toAlgHom.toRingHom).toAlgebra
  have : IsScalarTower (RatFunc k) ↥E F := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  have : IsScalarTower k (RatFunc k) F := IsScalarTower.of_algebraMap_eq (fun c => by
    change algebraMap k F c = algebraMap ↥E F (e (algebraMap k (RatFunc k) c))
    rw [e.commutes, ← IsScalarTower.algebraMap_apply])
  have : IsScalarTower k (RatFunc k) ↥E := IsScalarTower.of_algebraMap_eq (fun c => by
    change algebraMap k ↥E c = e (algebraMap k (RatFunc k) c)
    rw [e.commutes])
  have : Module.Finite (RatFunc k) ↥E :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc k) ↥E) e.surjective
  have : FiniteDimensional (RatFunc k) F := Module.Finite.trans ↥E F
  have : Algebra.IsSeparable (RatFunc k) ↥E := by
    refine ⟨fun y => ?_⟩
    obtain ⟨r, rfl⟩ := e.surjective y
    change IsSeparable (RatFunc k) (algebraMap (RatFunc k) ↥E r)
    exact isSeparable_algebraMap r
  have : Algebra.IsSeparable (RatFunc k) F := Algebra.IsSeparable.trans (RatFunc k) ↥E F
  exact AlgebraicCurve.RationalFunctionField.nonempty_place_of_ratFunc_tower k F

end S_AlgebraicCurve_nonempty_place_of_transcendental_of_finiteDimensional
end P2MW
export P2MW.S_AlgebraicCurve_nonempty_place_of_transcendental_of_finiteDimensional (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.nonempty_place_of_transcendental_of_finiteDimensional
    (k : Type*) [Field k] {F : Type*} [Field F] [Algebra k F] (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional ↥(IntermediateField.adjoin k ({x} : Set F)) F)
    [Algebra.IsSeparable ↥(IntermediateField.adjoin k ({x} : Set F)) F] :
    Nonempty (AlgebraicCurve.Place k F) := _root_.P2MW.S_AlgebraicCurve_nonempty_place_of_transcendental_of_finiteDimensional.solution k x hx hfin

end publicSection
