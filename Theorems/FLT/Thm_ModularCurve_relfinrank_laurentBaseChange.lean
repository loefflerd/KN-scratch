import Definitions.FLT.Def_ModularCurve_LaurentCoeff
import Mathlib.FieldTheory.Relrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.relfinrank_laurentBaseChange (L : Type*) [Field L] [Algebra ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (t : LaurentSeries ℚ) (ht : t ∈ F₀) (htr : Transcendental ℚ t) : IntermediateField.relfinrank (IntermediateField.adjoin L ({coeffEmb L t} : Set (LaurentSeries L))) (laurentBaseChange L F₀) = IntermediateField.relfinrank (IntermediateField.adjoin ℚ ({t} : Set (LaurentSeries ℚ))) F₀ := by sorry
