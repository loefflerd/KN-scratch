import Definitions.FLT.Def_ModularCurve_X0
import Mathlib.NumberTheory.ModularForms.Discriminant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit : UpperHalfPlane.qExpansion 1 ModularForm.discriminant = PowerSeries.map (Int.castRingHom ℂ) (PowerSeries.X * ModularCurve.dedekindEtaUnit) := by sorry
