import Definitions.FLT.Def_ModularCurve_MazurStepThreeInputs
import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.FLT.Def_AlgebraicCurve_DivisorPushPull
import Definitions.FLT.Def_ModularCurve_JLinePlaces
import Definitions.FLT.Def_ModularCurve_GenusNumerics
import Definitions.FLT.Def_ModularCurve_ModuliPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IntermediateField AlgebraicCurve AlgebraicCurve.RationalFunctionField ModularCurve IsDedekindDomain WithZero IsLocalRing
theorem ModularCurve.natCard_ord_jBar_eq_one_eq_nuThree (N : ℕ) [NeZero N]
    (h1 : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), 0 < v.ord (jBar N) → v.ord (jBar N) ∣ 3)
    [DecidableEq (AlgebraicClosure ℚ)]
    (hcount : Nat.card {v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) // 0 < v.ord (jBar N)} =
      Nat.card {x : ModuliPoint N (AlgebraicClosure ℚ) // ModuliPoint.j x = (0 : AlgebraicClosure ℚ)}) :
    Nat.card {v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) // v.ord (jBar N) = 1} = nuThree N := by sorry
