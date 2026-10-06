import Mathlib.FieldTheory.RatFunc.Basic

import Definitions.FLT.Def_AlgebraicCurve_AdelicIndex
import Definitions.FLT.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve
theorem RationalFunctionField.stichtenothGenusExists (K : Type*) [Field K] [DecidableEq (RatFunc K)] (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F] [IsCurveOver K F] (hC : ConstantsAreBase K F) :
    StichtenothGenusExists K F := by sorry
