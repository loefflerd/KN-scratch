import Definitions.FLT.Def_ModularCurve_X0
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_dedekindPsi_prime

open ModularCurve IntermediateField

noncomputable section

theorem solution {p : ℕ} (hp : p.Prime) : dedekindPsi p = p + 1 :=by
  rw [dedekindPsi, Finset.sum_filter, hp.divisors, Finset.sum_pair hp.one_lt.ne]
  simp [hp.squarefree, Nat.div_self hp.pos]

end

end S_ModularCurve_dedekindPsi_prime
end P2MW
export P2MW.S_ModularCurve_dedekindPsi_prime (solution)
