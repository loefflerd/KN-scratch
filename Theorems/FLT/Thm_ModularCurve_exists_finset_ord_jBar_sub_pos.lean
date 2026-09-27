import Definitions.FLT.Def_ModularCurve_MazurStepThreeInputs
import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.FLT.Def_AlgebraicCurve_DivisorPushPull
import Definitions.FLT.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.FLT.Def_AlgebraicCurve_RatFuncPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve
theorem ModularCurve.exists_finset_ord_jBar_sub_pos (N : ℕ) [NeZero N] (j₀ : AlgebraicClosure ℚ) :
    ∃ S : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)), ∀ v, v ∈ S ↔
      0 < v.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀) := by sorry
