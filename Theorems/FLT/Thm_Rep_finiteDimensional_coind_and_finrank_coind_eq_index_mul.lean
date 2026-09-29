import Mathlib.GroupTheory.Index
import Mathlib.RepresentationTheory.Coinduced

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory
theorem Rep.finiteDimensional_coind_and_finrank_coind_eq_index_mul {k G : Type u} [Field k] [Group G] (S : Subgroup G) [S.FiniteIndex]
    (N : Rep.{u} k S) [FiniteDimensional k N] :
    FiniteDimensional k (Rep.coind S.subtype N) ∧
      Module.finrank k (Rep.coind S.subtype N) = S.index * Module.finrank k N := by sorry
