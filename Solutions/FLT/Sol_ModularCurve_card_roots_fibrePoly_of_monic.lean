import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

import Definitions.FLT.Def_ModularCurve_FibrePoly
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_card_roots_fibrePoly_of_monic

open Polynomial ModularCurve

theorem solution {K : Type*} [Field K] [IsAlgClosed K]
    {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic) (a : K) :
    Multiset.card (fibrePoly Φ a).roots = Φ.natDegree := by
  rw [← (IsAlgClosed.splits (fibrePoly Φ a)).natDegree_eq_card_roots]
  exact hΦ.natDegree_map _

end S_ModularCurve_card_roots_fibrePoly_of_monic
end P2MW
export P2MW.S_ModularCurve_card_roots_fibrePoly_of_monic (solution)
