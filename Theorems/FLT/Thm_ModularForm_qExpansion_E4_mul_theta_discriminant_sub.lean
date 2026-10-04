import Mathlib.NumberTheory.ModularForms.Discriminant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.qExpansion_E4_mul_theta_discriminant_sub :
    UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₄ : UpperHalfPlane → ℂ) *
        PowerSeries.mk (fun n : ℕ => (n : ℂ) * (UpperHalfPlane.qExpansion 1 ModularForm.discriminant).coeff n)
      - 3 * PowerSeries.mk (fun n : ℕ => (n : ℂ) * (UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₄ : UpperHalfPlane → ℂ)).coeff n)
        * UpperHalfPlane.qExpansion 1 ModularForm.discriminant
      = UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₆ : UpperHalfPlane → ℂ) *
        UpperHalfPlane.qExpansion 1 ModularForm.discriminant := by sorry
