import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_divisor_eq_max_ord_sub_algebraMap

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (x : F) (hx : Transcendental K x) (a : K) :
    ∃ D : Divisor K F, ∀ v : Place K F, D v = max 0 (v.ord (x - algebraMap K F a)) := by
  classical
  have hxa : x - algebraMap K F a ≠ 0 := by
    intro h
    apply hx
    rw [sub_eq_zero] at h
    rw [h]
    exact isAlgebraic_algebraMap a
  obtain ⟨P, hP, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) (x - algebraMap K F a) hxa
  exact ⟨P.mapRange (fun n => max 0 n) (by simp), fun v => by rw [Finsupp.mapRange_apply, hP v]⟩

end S_AlgebraicCurve_exists_divisor_eq_max_ord_sub_algebraMap
end P2MW
export P2MW.S_AlgebraicCurve_exists_divisor_eq_max_ord_sub_algebraMap (solution)
