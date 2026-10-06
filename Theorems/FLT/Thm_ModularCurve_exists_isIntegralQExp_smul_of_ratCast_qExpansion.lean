import Definitions.FLT.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.exists_isIntegralQExp_smul_of_ratCast_qExpansion (M : ℕ) [NeZero M] {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 f).coeff n = (r : ℂ)) :
    ∃ (D : ℤ) (p : PowerSeries ℤ), D ≠ 0 ∧
      ModularCurve.IsIntegralQExp ((D : ℂ) • (⇑f : UpperHalfPlane → ℂ)) p := by sorry
