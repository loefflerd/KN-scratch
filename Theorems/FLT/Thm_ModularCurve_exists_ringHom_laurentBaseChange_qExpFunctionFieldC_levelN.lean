import Mathlib
import Definitions.FLT.Def_ModularCurve_LevelNFunctionField
import Definitions.FLT.Def_ModularCurve_X1
import Definitions.FLT.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups
theorem ModularCurve.exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN
    (M : ℕ) [NeZero M] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hT : ModularGroup.T ∈ Γ)
    (ι : AlgebraicClosure ℚ →+* ℂ)
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring M) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring M) K]
    [IsFractionRing (ModularCurve.LevelN.ring M) K] :
    ∃ Φ : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
        (ModularCurve.qExpFunctionFieldC ℚ Γ) →+* K,
      (∀ c : AlgebraicClosure ℚ,
          Φ (algebraMap (AlgebraicClosure ℚ)
            (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
              (ModularCurve.qExpFunctionFieldC ℚ Γ)) c) =
            algebraMap ℂ K (ι c)) ∧
      (∀ y : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.qExpFunctionFieldC ℚ Γ),
          (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ) →
          Φ y = algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M)) ∧
      ∀ γ ∈ Γ, ∀ (hst : ∀ G ∈ ModularCurve.LevelN.ring M,
          (fun τ : UpperHalfPlane => G (γ⁻¹ • τ)) ∈ ModularCurve.LevelN.ring M)
        (φ : K ≃ₐ[ℂ] K),
        (∀ (G : UpperHalfPlane → ℂ) (hG : G ∈ ModularCurve.LevelN.ring M),
            φ (algebraMap (ModularCurve.LevelN.ring M) K ⟨G, hG⟩) =
              algebraMap (ModularCurve.LevelN.ring M) K
                ⟨fun τ : UpperHalfPlane => G (γ⁻¹ • τ), hst G hG⟩) →
        ∀ u, φ (Φ u) = Φ u := by sorry
