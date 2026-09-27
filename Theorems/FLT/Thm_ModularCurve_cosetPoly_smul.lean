import Definitions.FLT.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.cosetPoly_smul (ℓ : ℕ) (hℓ : ℓ.Prime) (F : UpperHalfPlane → ℂ) (hF : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane), F (γ • τ) = F τ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) : (Polynomial.X - Polynomial.C (F (ModularForm.heckeDiagMatrix ℓ • γ • τ))) * ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (F (ModularForm.heckeMatrix ℓ (b : ℕ) • γ • τ))) = (Polynomial.X - Polynomial.C (F (ModularForm.heckeDiagMatrix ℓ • τ))) * ∏ b : Fin ℓ, (Polynomial.X - Polynomial.C (F (ModularForm.heckeMatrix ℓ (b : ℕ) • τ))) := by sorry
