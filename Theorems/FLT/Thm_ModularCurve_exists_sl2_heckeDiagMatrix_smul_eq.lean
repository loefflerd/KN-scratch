import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Definitions.FLT.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.exists_sl2_heckeDiagMatrix_smul_eq (N : ℕ) [NeZero N] (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) : ∃ γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ, (∀ τ : UpperHalfPlane, ModularForm.heckeDiagMatrix N • γ • τ = γ' • ModularForm.heckeDiagMatrix N • τ) ∧ ∀ τ : UpperHalfPlane, UpperHalfPlane.denom (γ' : Matrix.GeneralLinearGroup (Fin 2) ℝ) (((ModularForm.heckeDiagMatrix N • τ : UpperHalfPlane)) : ℂ) = UpperHalfPlane.denom (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) (τ : ℂ) := by sorry
