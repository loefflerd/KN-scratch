import Mathlib.Analysis.CStarAlgebra.Classes

import Definitions.FLT.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem UpperHalfPlane.eq_of_forall_qCoeff_eq {f g : UpperHalfPlane → ℂ} (hfper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1) (hfhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (hfbdd : UpperHalfPlane.IsBoundedAtImInfty f) (hgper : Function.Periodic (g ∘ UpperHalfPlane.ofComplex) 1) (hghol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) g) (hgbdd : UpperHalfPlane.IsBoundedAtImInfty g) (h : ∀ n : ℕ, ModularFormClass.qCoeff f n = ModularFormClass.qCoeff g n) : f = g := by sorry
