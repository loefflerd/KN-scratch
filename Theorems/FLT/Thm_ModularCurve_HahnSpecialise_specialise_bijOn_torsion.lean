import Definitions.FLT.Def_ModularCurve_HahnSpecialise

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.B3 ModularCurve.HahnSpecialise
open ModularCurve.TatePoint (Qbar H CycSubH)
open scoped Classical
theorem ModularCurve.HahnSpecialise.specialise_bijOn_torsion (E : WeierstrassCurve H) (hE : IntegralCoeffs E)
    (hΔ : (specialFibre E).Δ ≠ 0) (N : ℕ) [NeZero N] :
    Set.BijOn (specialise E hE hΔ) {P | N • P = 0} {Q | N • Q = 0} := by sorry
