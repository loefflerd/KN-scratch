import Definitions.FLT.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
theorem ModularCurve.transcendental_and_finiteDimensional_adjoin_laurentBaseChange_of_coe_eq_coeffEmb
    (L : Type) [Field L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (j : ↥F₀) (hj : Transcendental ℚ j)
    [FiniteDimensional ↥(IntermediateField.adjoin ℚ ({j} : Set ↥F₀)) ↥F₀]
    (jb : ↥(laurentBaseChange L F₀))
    (hjb : (jb : LaurentSeries L) = coeffEmb L ((j : ↥F₀) : LaurentSeries ℚ)) :
    Transcendental L jb ∧
      FiniteDimensional ↥(IntermediateField.adjoin L ({jb} : Set ↥(laurentBaseChange L F₀)))
        ↥(laurentBaseChange L F₀) := by sorry
