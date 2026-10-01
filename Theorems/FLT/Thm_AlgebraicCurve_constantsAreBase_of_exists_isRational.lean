import Definitions.FLT.Def_AlgebraicCurve_AdelicIndex
import Definitions.FLT.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem AlgebraicCurve.constantsAreBase_of_exists_isRational {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.HasPrincipalDivisors K F]
    (v₀ : AlgebraicCurve.Place K F) (hrat : v₀.IsRational) (hdeg : v₀.deg ≠ 0) :
    AlgebraicCurve.ConstantsAreBase K F := by sorry
