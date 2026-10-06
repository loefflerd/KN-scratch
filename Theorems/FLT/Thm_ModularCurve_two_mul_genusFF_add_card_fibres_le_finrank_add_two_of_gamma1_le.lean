import Definitions.FLT.Def_AlgebraicCurve_Repartitions
import Definitions.FLT.Def_ModularCurve_JqCoeff
import Definitions.FLT.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.two_mul_genusFF_add_card_fibres_le_finrank_add_two_of_gamma1_le
    (M : ℕ) [NeZero M] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hΓ : CongruenceSubgroup.Gamma1 M ≤ Γ)
    (y : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ)) :
    2 * AlgebraicCurve.genusFF (AlgebraicClosure ℚ)
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) +
        Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) //
            P.ord y < 0} +
        Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) //
            0 < P.ord y} +
        Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) //
            0 < P.ord (y - 1728)} ≤
      Module.finrank
          (IntermediateField.adjoin (AlgebraicClosure ℚ)
            ({y} : Set (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
              (ModularCurve.qExpFunctionFieldC ℚ Γ))))
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) +
        2 := by sorry
