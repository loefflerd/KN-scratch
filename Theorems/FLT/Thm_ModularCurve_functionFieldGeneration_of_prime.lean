module

public import Definitions.FLT.Def_ModularCurve_X0

import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_functionFieldGeneration_of_prime

open ModularCurve IntermediateField

noncomputable section

theorem solution {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) : FunctionFieldGeneration ℓ :=by
  intro d hd hne
  have := hne
  rcases (Nat.dvd_prime hℓ).mp hd with rfl | rfl
  · rw [qExpand_one_apply]
    exact subset_adjoin ℚ _ (Set.mem_insert _ _)
  · exact subset_adjoin ℚ _ (Set.mem_insert_of_mem _ rfl)

end

end S_ModularCurve_functionFieldGeneration_of_prime
end P2MW
export P2MW.S_ModularCurve_functionFieldGeneration_of_prime (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve IntermediateField
theorem ModularCurve.functionFieldGeneration_of_prime {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) : FunctionFieldGeneration ℓ := _root_.P2MW.S_ModularCurve_functionFieldGeneration_of_prime.solution hℓ

end publicSection
