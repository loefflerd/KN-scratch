import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

import Definitions.FLT.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularForm.isBoundedAtImInfty_heckeT {f : UpperHalfPlane → ℂ} (hf : UpperHalfPlane.IsBoundedAtImInfty f) (k : ℤ) (p : ℕ) : UpperHalfPlane.IsBoundedAtImInfty (ModularForm.heckeT k p f) := by sorry
