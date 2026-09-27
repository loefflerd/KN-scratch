import Definitions.FLT.Def_ModularCurve_PhiGen
import Definitions.FLT.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket {K : Type*} [Field K] (d : ℕ) [NeZero d] (hbase : ∀ (p : ℕ) [Fact (Nat.Prime p)], p ∣ d → jqNModC K p ∉ IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) : Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) ({jqNModC K d} : Set (LaurentSeries K))) = dedekindPsi d := by sorry
