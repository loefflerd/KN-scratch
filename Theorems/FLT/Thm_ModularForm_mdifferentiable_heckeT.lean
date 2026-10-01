import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

import Definitions.FLT.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularForm.mdifferentiable_heckeT {f : UpperHalfPlane → ℂ} (hf : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (k : ℤ) (p : ℕ) : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (ModularForm.heckeT k p f) := by sorry
