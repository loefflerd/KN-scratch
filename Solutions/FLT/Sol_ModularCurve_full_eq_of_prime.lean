import Definitions.FLT.Def_ModularCurve_X0
import Theorems.FLT.Thm_ModularCurve_functionFieldGeneration_iff_full_eq
import Theorems.FLT.Thm_ModularCurve_functionFieldGeneration_of_prime
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_full_eq_of_prime

open ModularCurve IntermediateField

noncomputable section

theorem solution {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) : modularFunctionFieldFull ℓ = modularFunctionField ℓ :=
  (ModularCurve.functionFieldGeneration_iff_full_eq ℓ).mp (ModularCurve.functionFieldGeneration_of_prime hℓ)

end

end S_ModularCurve_full_eq_of_prime
end P2MW
export P2MW.S_ModularCurve_full_eq_of_prime (solution)
