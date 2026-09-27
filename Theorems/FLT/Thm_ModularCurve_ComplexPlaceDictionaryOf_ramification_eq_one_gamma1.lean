import Mathlib
import Definitions.FLT.Def_ModularCurve_X1
import Definitions.FLT.Def_ModularCurve_ComplexPlaceDictionaryOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
theorem ModularCurve.ComplexPlaceDictionaryOf.ramification_eq_one_gamma1
    (M : ℕ) [NeZero M] (hM : 4 ≤ M)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))
    (D : ModularCurve.ComplexPlaceDictionaryOf (CongruenceSubgroup.Gamma1 M) F₀) (τ : UpperHalfPlane) :
    D.ramification τ = 1 := by sorry
