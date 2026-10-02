module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs

@[expose] public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace EisensteinSeries

noncomputable def eisensteinG (N : ℕ) (k : ℤ) (a : Fin 2 → ZMod N) (z : UpperHalfPlane) : ℂ :=
  ∑' v : {v : Fin 2 → ℤ // ((↑) : ℤ → ZMod N) ∘ v = a}, eisSummand k v.1 z

end EisensteinSeries

end publicSection
