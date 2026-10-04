import Definitions.FLT.Def_ModularCurve_JqCoeff
import Definitions.FLT.Def_ModularCurve_LevelNFunctionField

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial
open scoped MatrixGroups
theorem ModularCurve.LevelN.exists_monic_eval_eq_zero_coeff_eq_aeval_inv_div_of_forall_valuation_le_one
    (M : ℕ) [NeZero M]
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring M) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring M) K]
    [IsFractionRing (ModularCurve.LevelN.ring M) K]
    (σ : SL(2, ℤ) →* (K ≃ₐ[ℂ] K))
    (hker : σ.ker = CongruenceSubgroup.Gamma M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)))
    (hfixed : IntermediateField.fixedField σ.range =
      IntermediateField.adjoin ℂ
        ({algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M)} : Set K))
    (E : K →ₐ[ℂ] LaurentSeries ℂ)
    (hEj : E (algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M)) =
      ModularCurve.qExpand ℂ M (ModularCurve.jqModC ℂ))
    (z : K) (hz : ∀ γ : SL(2, ℤ), Valued.v (E (σ γ z)) ≤ 1) :
    ∃ P : K[X], P.Monic ∧ P.eval z = 0 ∧
      ∀ i : ℕ, ∃ p q : ℂ[X], q.coeff 0 ≠ 0 ∧
        P.coeff i =
          aeval (algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M))⁻¹ p /
            aeval (algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M))⁻¹ q := by sorry
