import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.RingTheory.PowerSeries.PiTopology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped PowerSeries.WithPiTopology
theorem ModularCurve.qExpansion_discriminant_eq_X_mul_tprod : UpperHalfPlane.qExpansion 1 ModularForm.discriminant = PowerSeries.X * ∏' n : ℕ, ((1 : PowerSeries ℂ) - PowerSeries.X ^ (n + 1)) ^ 24 := by sorry
