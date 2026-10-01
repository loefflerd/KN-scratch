import Mathlib.Analysis.CStarAlgebra.Classes

import Definitions.FLT.Def_FLTPrelim_Modularity
import Definitions.FLT.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem UpperHalfPlane.qCoeff_heckeU {f : UpperHalfPlane → ℂ} (hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1) (hhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f) (k : ℤ) {p : ℕ} (hp : p ≠ 0) (n : ℕ) : ModularFormClass.qCoeff (ModularForm.heckeU k p f) n = ModularForm.coeffHeckeU p (ModularFormClass.qCoeff f) n := by sorry
