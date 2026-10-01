import Mathlib.NumberTheory.ModularForms.Discriminant

import Definitions.FLT.Def_ModularCurve_PrimCosetReps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
theorem ModularCurve.ModularPolynomialData.eval_E4_cube_div_discriminant_coset_eq_zero (N : ℕ) [NeZero N]
    (data : ModularCurve.ModularPolynomialData N) {a b d : ℕ} (habd : (a, b, d) ∈ ModularCurve.primCosetReps N)
    (τ τ' : ℍ) (hτ' : (τ' : ℂ) = ((a : ℂ) * τ + b) / d) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ℂ)
        ((ModularForm.E₄ : ℍ → ℂ) τ ^ 3 / ModularForm.discriminant τ))).eval
      ((ModularForm.E₄ : ℍ → ℂ) τ' ^ 3 / ModularForm.discriminant τ') = 0 := by sorry
