import Definitions.FLT.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups in
theorem ModularCurve.finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
    {K₀ K : Type*} [Field K₀] [Field K] (φ : K₀ →+* K) (Γ : Subgroup SL(2, ℤ))
    (x₀ : ModularCurve.qExpFunctionFieldC K₀ Γ) (x : ModularCurve.qExpFunctionFieldC K Γ)
    (hx₀ : Transcendental K₀ (x₀ : LaurentSeries K₀))
    (hx : (x : LaurentSeries K) = ModularCurve.coeffMap φ (x₀ : LaurentSeries K₀))
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
      (ModularCurve.qExpFunctionFieldC K Γ)] :
    FiniteDimensional (IntermediateField.adjoin K₀ ({x₀} : Set (ModularCurve.qExpFunctionFieldC K₀ Γ)))
        (ModularCurve.qExpFunctionFieldC K₀ Γ) ∧
      Module.finrank (IntermediateField.adjoin K₀ ({x₀} : Set (ModularCurve.qExpFunctionFieldC K₀ Γ)))
          (ModularCurve.qExpFunctionFieldC K₀ Γ) ≤
        Module.finrank (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
          (ModularCurve.qExpFunctionFieldC K Γ) := by sorry
