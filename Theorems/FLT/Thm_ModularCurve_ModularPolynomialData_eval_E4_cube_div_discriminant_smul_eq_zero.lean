import Mathlib.NumberTheory.ModularForms.Discriminant

import Definitions.FLT.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
theorem ModularCurve.ModularPolynomialData.eval_E4_cube_div_discriminant_smul_eq_zero (N : ℕ) [NeZero N]
    (data : ModularCurve.ModularPolynomialData N) (σ σ' : ℍ) (hσ' : (σ' : ℂ) = (N : ℂ) * σ) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ℂ)
        ((ModularForm.E₄ : ℍ → ℂ) σ ^ 3 / ModularForm.discriminant σ))).eval
      ((ModularForm.E₄ : ℍ → ℂ) σ' ^ 3 / ModularForm.discriminant σ') = 0 := by sorry
