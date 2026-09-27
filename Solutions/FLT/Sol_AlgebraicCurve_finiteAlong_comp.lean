import Definitions.FLT.Def_AlgebraicCurve_Correspondence
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_finiteAlong_comp

set_option autoImplicit false

open AlgebraicCurve

theorem solution {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'') (hφ : FiniteAlong K φ) (hχ : FiniteAlong K χ) : FiniteAlong K (χ.comp φ) := by
  let := algebraAlong φ
  let := algebraAlong χ
  let := algebraAlong (χ.comp φ)
  have : IsScalarTower F F' F'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite F F' := hφ
  have : Module.Finite F' F'' := hχ
  exact Module.Finite.trans F' F''

end S_AlgebraicCurve_finiteAlong_comp
end P2MW
export P2MW.S_AlgebraicCurve_finiteAlong_comp (solution)
