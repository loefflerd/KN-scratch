import Mathlib
import Definitions.FLT.Def_ModularCurve_X1
import Definitions.FLT.Def_ModularCurve_JqCoeff
import Definitions.FLT.Def_ModularCurve_X0ModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.dedekindPsi_le_finrank_adjoin_qExpFunctionFieldC_gamma0
    (K : Type*) [Field K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (x : ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M))
    (hx : (x : LaurentSeries K) = ModularCurve.jqModC K)
    [FiniteDimensional
      (IntermediateField.adjoin K
        ({x} : Set (ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M))))
      (ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M))] :
    ModularCurve.dedekindPsi M ≤
      Module.finrank
        (IntermediateField.adjoin K
          ({x} : Set (ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M))))
        (ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M)) := by sorry
