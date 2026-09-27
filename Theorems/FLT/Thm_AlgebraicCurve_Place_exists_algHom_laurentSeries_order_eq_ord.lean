import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.FLT.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve
theorem AlgebraicCurve.Place.exists_algHom_laurentSeries_order_eq_ord {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F) (hw : w.deg = 1) :
    ∃ φ : F →ₐ[K] LaurentSeries K, ∀ x : F, (φ x).order = w.ord x := by sorry
