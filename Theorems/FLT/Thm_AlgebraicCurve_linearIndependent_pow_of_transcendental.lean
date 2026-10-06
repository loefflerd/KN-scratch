import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.RingTheory.Algebraic.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve
theorem linearIndependent_pow_of_transcendental {K : Type*} {A : Type*} [CommRing K] [CommRing A] [Algebra K A] {x : A} (hx : Transcendental K x) :
    LinearIndependent K (fun j : ℕ => x ^ j) := by sorry
