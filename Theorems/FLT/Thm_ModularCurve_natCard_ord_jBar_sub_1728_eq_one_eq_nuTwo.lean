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
theorem ModularCurve.natCard_ord_jBar_sub_1728_eq_one_eq_nuTwo (N : ℕ) [NeZero N]
    (h2 : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), 0 < v.ord (jBar N - 1728) → v.ord (jBar N - 1728) ∣ 2)
    [DecidableEq (AlgebraicClosure ℚ)]
    (hcount : Nat.card {v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) // 0 < v.ord (jBar N - 1728)} =
      Nat.card {x : ModuliPoint N (AlgebraicClosure ℚ) // ModuliPoint.j x = (1728 : AlgebraicClosure ℚ)}) :
    Nat.card {v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) // v.ord (jBar N - 1728) = 1} = nuTwo N := by sorry
