import Definitions.FLT.Def_ModularCurve_SpecialisationBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.TatePoint ModularCurve.B3
theorem ModularCurve.B3.specialisationEquivariance_level (N : ℕ) [NeZero N] (j₀ : Qbar) :
    ∃ β : CycSubH (nearCurve j₀) N ≃ CycSub (WeierstrassCurve.ofJ j₀) N,
      ∀ G G' : CycSubH (nearCurve j₀) N,
        (∃ m : HahnSeries.monodromy Qbar, b3Act j₀ m G.1 = G'.1) ↔
          SameOrbit (WeierstrassCurve.ofJ j₀) (β G).1 (β G').1 := by sorry
