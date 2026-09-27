import Mathlib.Algebra.Polynomial.Splits

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem Polynomial.mem_range_of_eval_eq_const {F L : Type*} [Field F] [Field L] [Algebra F L] (g : Polynomial F) (x : L) (s : Finset L) (hcard : g.natDegree < s.card) (hval : ∀ y ∈ s, Polynomial.aeval y g = x) : x ∈ (algebraMap F L).range := by sorry
