import Definitions.FLT.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.FLT.Def_ModularCurve_LevelNFunctionField

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups IntermediateField
theorem ModularCurve.LevelN.exists_place_ord_jGen_eq_three_two_and_stabilizer_subset_zpowers
    (M : ℕ) [NeZero M] (hM : 2 ≤ M)
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring M) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring M) K] [IsFractionRing (ModularCurve.LevelN.ring M) K]
    (hst : ∀ (δ : SL(2, ℤ)), ∀ G ∈ ModularCurve.LevelN.ring M,
      (fun τ : UpperHalfPlane => G (δ • τ)) ∈ ModularCurve.LevelN.ring M)
    (σ : SL(2, ℤ) →* (K ≃ₐ[ℂ] K))
    (hσ : ∀ (γ : SL(2, ℤ)) (G : UpperHalfPlane → ℂ) (hG : G ∈ ModularCurve.LevelN.ring M),
      σ γ (algebraMap (ModularCurve.LevelN.ring M) K ⟨G, hG⟩) =
        algebraMap (ModularCurve.LevelN.ring M) K ⟨fun τ : UpperHalfPlane => G (γ⁻¹ • τ), hst γ⁻¹ G hG⟩)
    (hker : σ.ker = CongruenceSubgroup.Gamma M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)))
    (hfixed : IntermediateField.fixedField σ.range =
      ℂ⟮algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M)⟯)
    (hfin : FiniteDimensional ℂ⟮algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M)⟯ K)
    (hgal : IsGalois ℂ⟮algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M)⟯ K) :
    (∃ W : AlgebraicCurve.Place ℂ K,
      W.ord (algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M)) = 3 ∧
      ∀ g : K ≃ₐ[ℂ⟮algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M)⟯] K,
        AlgebraicCurve.SemilinearAut.ofAlgAut (g.restrictScalars ℂ) • W = W →
        ∃ k : ℕ, g.restrictScalars ℂ = σ (ModularGroup.S * ModularGroup.T) ^ k) ∧
    (∃ W : AlgebraicCurve.Place ℂ K,
      W.ord (algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M) - 1728) = 2 ∧
      ∀ g : K ≃ₐ[ℂ⟮algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M)⟯] K,
        AlgebraicCurve.SemilinearAut.ofAlgAut (g.restrictScalars ℂ) • W = W →
        ∃ k : ℕ, g.restrictScalars ℂ = σ ModularGroup.S ^ k) := by sorry
