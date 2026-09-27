import Mathlib
import Definitions.FLT.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.finrank_adjoin_qExpFunctionFieldC_le_of_valuationSubring
    {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
    {k : Type*} [Field k] (π : A →+* k)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hF : ∃ t : ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ),
      Transcendental L t ∧
        FiniteDimensional
          (IntermediateField.adjoin L
            ({t} : Set (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))))
          (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)))
    (a b : PowerSeries ℤ)
    (X : ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (hX : (X : LaurentSeries L) = ModularCurve.intSeriesC L a / ModularCurve.intSeriesC L b)
    (x : ModularCurve.qExpFunctionFieldC k Γ)
    (hx : (x : LaurentSeries k) = ModularCurve.intSeriesC k a / ModularCurve.intSeriesC k b)
    (htr : Transcendental k x) :
    FiniteDimensional (IntermediateField.adjoin k ({x} : Set (ModularCurve.qExpFunctionFieldC k Γ)))
        (ModularCurve.qExpFunctionFieldC k Γ) ∧
      Module.finrank (IntermediateField.adjoin k ({x} : Set (ModularCurve.qExpFunctionFieldC k Γ)))
          (ModularCurve.qExpFunctionFieldC k Γ) ≤
        Module.finrank
          (IntermediateField.adjoin L
            ({X} : Set (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))))
          (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)) := by sorry
