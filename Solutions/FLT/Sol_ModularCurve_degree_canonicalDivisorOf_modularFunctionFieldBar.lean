import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.TotallySplit

import Definitions.FLT.Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2
import Definitions.FLT.Def_ModularCurve_JLinePlacesBar
import Theorems.FLT.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.FLT.Thm_AlgebraicCurve_degree_canonicalDivisor_eq_of_isAlgClosed
import Theorems.FLT.Thm_AlgebraicCurve_instIsCurveOverRatFunc
import Theorems.FLT.Thm_ModularCurve_essFiniteType_modularFunctionFieldBar
import Theorems.FLT.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_of_neZero
import Theorems.FLT.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_degree_canonicalDivisorOf_modularFunctionFieldBar
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

attribute [local instance] ModularCurve.instDecidableEqRatFuncAlgebraicClosure

open ModularCurve AlgebraicCurve

theorem solution (N : ℕ) [NeZero N]
    [AlgebraicCurve.HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.modularFunctionFieldBar N))]
    {ω : Ω[↥(ModularCurve.modularFunctionFieldBar N)⁄(AlgebraicClosure ℚ)]} (hω : ω ≠ 0) :
    (AlgebraicCurve.canonicalDivisorOf hω).degree
      = 2 * (AlgebraicCurve.genus (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) : ℤ) - 2 := by
  have : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  have : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) := IsCurveOver.hasPrincipalDivisors
  have : Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
    essFiniteType_modularFunctionFieldBar N
  have hDCG : ∀ w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N), w.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver
  let algRE : Algebra (RatFunc (AlgebraicClosure ℚ)) ↥(jLineBar N) := (jLineBarRingEquiv N).toRingHom.toAlgebra
  let algRF : Algebra (RatFunc (AlgebraicClosure ℚ)) ↥(modularFunctionFieldBar N) :=
    ((algebraMap ↥(jLineBar N) ↥(modularFunctionFieldBar N)).comp (jLineBarRingEquiv N).toRingHom).toAlgebra
  have : IsScalarTower (RatFunc (AlgebraicClosure ℚ)) ↥(jLineBar N) ↥(modularFunctionFieldBar N) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)) ↥(modularFunctionFieldBar N) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    show algebraMap _ _ a = algebraMap ↥(jLineBar N) ↥(modularFunctionFieldBar N) (jLineBarRingEquiv N (algebraMap _ _ a))
    rw [jLineBarRingEquiv_algebraMap]
    rfl
  have : Module.Finite (RatFunc (AlgebraicClosure ℚ)) ↥(jLineBar N) :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc (AlgebraicClosure ℚ)) ↥(jLineBar N))
      (jLineBarRingEquiv N).surjective
  have : FiniteDimensional ↥(jLineBar N) ↥(modularFunctionFieldBar N) :=
    finiteDimensional_adjoin_coeffEmb_jq_of_neZero N
  have hfinRF : Module.Finite (RatFunc (AlgebraicClosure ℚ)) ↥(modularFunctionFieldBar N) :=
    Module.Finite.trans ↥(jLineBar N) ↥(modularFunctionFieldBar N)
  have : Algebra.IsIntegral (RatFunc (AlgebraicClosure ℚ)) ↥(modularFunctionFieldBar N) :=
    Algebra.IsIntegral.of_finite _ _
  have : CharZero ↥(modularFunctionFieldBar N) :=
    charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) _).injective
  have : PerfectField (RatFunc (AlgebraicClosure ℚ)) := PerfectField.ofCharZero
  have : Algebra.IsSeparable (RatFunc (AlgebraicClosure ℚ)) ↥(modularFunctionFieldBar N) :=
    Algebra.IsSeparable.of_integral _ _
  have : IsCurveOver (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)) :=
    AlgebraicCurve.instIsCurveOverRatFunc (AlgebraicClosure ℚ)
  have : Algebra.EssFiniteType (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ)) :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors (Polynomial (AlgebraicClosure ℚ)))
  have : Algebra.EssFiniteType (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)) :=
    Algebra.EssFiniteType.comp (AlgebraicClosure ℚ) (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ))
  have hDCGR : ∀ v : Place (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)), v.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver
  have : HasCanonicalLocalResidueKStar (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) := inferInstance
  have : HasSeparableResidue (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) := inferInstance
  exact AlgebraicCurve.degree_canonicalDivisor_eq_of_isAlgClosed hω

end S_ModularCurve_degree_canonicalDivisorOf_modularFunctionFieldBar
end P2MW
export P2MW.S_ModularCurve_degree_canonicalDivisorOf_modularFunctionFieldBar (solution)
