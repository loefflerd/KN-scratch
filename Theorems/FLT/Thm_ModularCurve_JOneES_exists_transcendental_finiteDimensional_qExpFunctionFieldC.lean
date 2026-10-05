import Definitions.FLT.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ) :
    ∃ x : ModularCurve.qExpFunctionFieldC ℚ Γ, Transcendental ℚ x ∧
      FiniteDimensional
        (IntermediateField.adjoin ℚ ({x} : Set (ModularCurve.qExpFunctionFieldC ℚ Γ)))
        (ModularCurve.qExpFunctionFieldC ℚ Γ) := by sorry
