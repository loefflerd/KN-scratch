import Definitions.FLT.Def_ModularCurve_MazurStepThreeInputs
import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.FLT.Def_AlgebraicCurve_DivisorPushPull
import Definitions.FLT.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.FLT.Def_AlgebraicCurve_RatFuncPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve
theorem ModularCurve.sum_ord_jBar_sub_eq_dedekindPsi (N : ℕ) [NeZero N] (j₀ : AlgebraicClosure ℚ)
    (hdeg : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), w.deg = 1)
    (S : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)))
    (hS : ∀ v, v ∈ S ↔
      0 < v.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)) :
    ∑ v ∈ S, v.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀) =
      dedekindPsi N := by sorry
