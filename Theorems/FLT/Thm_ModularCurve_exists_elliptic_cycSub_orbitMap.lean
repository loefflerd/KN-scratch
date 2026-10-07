module

public import Definitions.FLT.Def_ModularCurve_EMD
public import Definitions.FLT.Def_ModularCurve_MazurStepThreeInputs

import Definitions.FLT.Def_ModularCurve_CycSubRootBridgeN
import Definitions.FLT.Def_ModularCurve_SpecialisationBridge
import Theorems.FLT.Thm_ModularCurve_exists_elliptic_cycSub_orbitMap_of_props
import Theorems.FLT.Thm_ModularCurve_TatePoint_fullKernelIsRootAt
import Theorems.FLT.Thm_ModularCurve_TatePoint_fullKernelInjAt
import Theorems.FLT.Thm_ModularCurve_TatePoint_fullKernelDiscAt
import Theorems.FLT.Thm_ModularCurve_TatePoint_b3Act_dictN_of_monodromy
import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_elliptic_cycSub_orbitMap
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero"

open ModularCurve AlgebraicCurve

theorem solution (N : ℕ) [NeZero N]
    (j₀ : AlgebraicClosure ℚ) :
    ∃ (E₀ : WeierstrassCurve (AlgebraicClosure ℚ)) (_ : E₀.IsElliptic), E₀.j = j₀ ∧
      ∃ f : CycSub E₀ N →
          {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) //
            0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)},
        (∀ H H' : CycSub E₀ N, f H = f H' ↔ SameOrbit E₀ H.1 H'.1) ∧
        ∀ w : {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) //
            0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)},
          ((w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)).ord
              (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)).toNat =
            Nat.card {H : CycSub E₀ N // f H = w} :=
  ModularCurve.exists_elliptic_cycSub_orbitMap_of_props N j₀
    (ModularCurve.TatePoint.fullKernelIsRootAt N) (ModularCurve.TatePoint.fullKernelInjAt N)
    (ModularCurve.TatePoint.fullKernelDiscAt N)
    (ModularCurve.TatePoint.b3Act_dictN_of_monodromy N j₀ (ModularCurve.TatePoint.fullKernelIsRootAt N)
      (ModularCurve.TatePoint.fullKernelInjAt N) (ModularCurve.TatePoint.fullKernelDiscAt N))

end S_ModularCurve_exists_elliptic_cycSub_orbitMap
end P2MW
export P2MW.S_ModularCurve_exists_elliptic_cycSub_orbitMap (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve
theorem ModularCurve.exists_elliptic_cycSub_orbitMap (N : ℕ) [NeZero N]
    (j₀ : AlgebraicClosure ℚ) :
    ∃ (E₀ : WeierstrassCurve (AlgebraicClosure ℚ)) (_ : E₀.IsElliptic), E₀.j = j₀ ∧
      ∃ f : CycSub E₀ N →
          {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) //
            0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)},
        (∀ H H' : CycSub E₀ N, f H = f H' ↔ SameOrbit E₀ H.1 H'.1) ∧
        ∀ w : {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) //
            0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)},
          ((w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)).ord
              (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)).toNat =
            Nat.card {H : CycSub E₀ N // f H = w} := _root_.P2MW.S_ModularCurve_exists_elliptic_cycSub_orbitMap.solution N j₀

end publicSection
