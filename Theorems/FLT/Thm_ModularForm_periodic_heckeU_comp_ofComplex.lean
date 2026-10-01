import Mathlib.Analysis.Complex.UpperHalfPlane.Topology

import Definitions.FLT.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularForm.periodic_heckeU_comp_ofComplex {f : UpperHalfPlane → ℂ} (hf : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1) (k : ℤ) (p : ℕ) : Function.Periodic (ModularForm.heckeU k p f ∘ UpperHalfPlane.ofComplex) 1 := by sorry
