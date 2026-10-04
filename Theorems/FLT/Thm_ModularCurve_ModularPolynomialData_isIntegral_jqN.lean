module

public import Definitions.FLT.Def_ModularCurve_X0

import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_isIntegral_jqN

open ModularCurve IntermediateField

noncomputable section

theorem solution {N : ℕ} [NeZero N] (data : ModularPolynomialData N) : IsIntegral ℚ⟮jq⟯ (jqN N) :=by
  refine ⟨data.toAdjoin, data.toAdjoin_monic, ?_⟩
  rw [ModularPolynomialData.toAdjoin, Polynomial.eval₂_map, algebraMap_comp_evalAtJGen]
  exact data.eval_eq_zero

end

end S_ModularCurve_ModularPolynomialData_isIntegral_jqN
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_isIntegral_jqN (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve IntermediateField
theorem ModularCurve.ModularPolynomialData.isIntegral_jqN {N : ℕ} [NeZero N] (data : ModularPolynomialData N) : IsIntegral ℚ⟮jq⟯ (jqN N) := _root_.P2MW.S_ModularCurve_ModularPolynomialData_isIntegral_jqN.solution data

end publicSection
