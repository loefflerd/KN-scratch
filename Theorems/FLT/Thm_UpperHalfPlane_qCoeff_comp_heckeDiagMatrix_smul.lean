import Definitions.FLT.Def_ModularForm_HeckeOperator
import Definitions.FLT.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul {f : UpperHalfPlane → ℂ} (hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1) (hhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f) {d : ℕ} (hd : d ≠ 0) (n : ℕ) : ModularFormClass.qCoeff (fun τ ↦ f (ModularForm.heckeDiagMatrix d • τ)) n = if d ∣ n then ModularFormClass.qCoeff f (n / d) else 0 := by sorry
