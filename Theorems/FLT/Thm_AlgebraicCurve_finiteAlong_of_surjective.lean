module

public import Definitions.FLT.Def_AlgebraicCurve_Correspondence

import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_finiteAlong_of_surjective

open AlgebraicCurve

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') (hφ : Function.Surjective φ) : FiniteAlong K φ := by
  let := algebraAlong φ
  exact Module.Finite.of_surjective (Algebra.linearMap F F') hφ

end S_AlgebraicCurve_finiteAlong_of_surjective
end P2MW
export P2MW.S_AlgebraicCurve_finiteAlong_of_surjective (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
theorem AlgebraicCurve.finiteAlong_of_surjective {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') (hφ : Function.Surjective φ) : FiniteAlong K φ := _root_.P2MW.S_AlgebraicCurve_finiteAlong_of_surjective.solution φ hφ

end publicSection
