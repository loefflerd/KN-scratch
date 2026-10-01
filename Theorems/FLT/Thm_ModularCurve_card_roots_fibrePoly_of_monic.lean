import Mathlib.RingTheory.SimpleRing.Principal

import Definitions.FLT.Def_ModularCurve_FibrePoly

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial
namespace ModularCurve
theorem card_roots_fibrePoly_of_monic {K : Type*} [Field K] [IsAlgClosed K]
    {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic) (a : K) :
    Multiset.card (fibrePoly Φ a).roots = Φ.natDegree := by sorry
