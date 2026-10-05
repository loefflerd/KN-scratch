module

public import Definitions.FLT.Def_AlgebraicCurve_Correspondence

import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_separableAlong_of_charZero

open AlgebraicCurve

theorem solution {K F F₁ : Type*} [Field K] [Field F] [Field F₁] [Algebra K F] [Algebra K F₁] [CharZero F] (φ : F →ₐ[K] F₁) (hφ : φ.toRingHom.IsIntegral) : SeparableAlong K φ := by
  let := algebraAlong φ
  have := isIntegral_along φ hφ
  exact Algebra.IsSeparable.of_integral F F₁

end S_AlgebraicCurve_separableAlong_of_charZero
end P2MW
export P2MW.S_AlgebraicCurve_separableAlong_of_charZero (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
theorem AlgebraicCurve.separableAlong_of_charZero {K F F₁ : Type*} [Field K] [Field F] [Field F₁] [Algebra K F] [Algebra K F₁] [CharZero F] (φ : F →ₐ[K] F₁) (hφ : φ.toRingHom.IsIntegral) : SeparableAlong K φ := _root_.P2MW.S_AlgebraicCurve_separableAlong_of_charZero.solution φ hφ

end publicSection
