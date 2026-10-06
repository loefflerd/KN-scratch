import Definitions.FLT.Def_ModularCurve_JqCoeff
import Definitions.FLT.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups IntermediateField
theorem ModularCurve.LevelN.Descent.fixer_le (M : ℕ) [NeZero M]
    (K : Type*) [Field K] [Algebra ℂ K] (t : K)
    (σ : SL(2, ℤ) →* (K ≃ₐ[ℂ] K)) (hker : σ.ker = CongruenceSubgroup.Gamma M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)))
    (hfin : FiniteDimensional ℂ⟮t⟯ K) (hgal : IsGalois ℂ⟮t⟯ K)
    (hdeg : Module.finrank ℂ⟮t⟯ K = (CongruenceSubgroup.Gamma M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index)
    (ι : AlgebraicClosure ℚ →+* ℂ)
    (Φ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
        (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))) →+* K)
    (E' : K →ₐ[ℂ] LaurentSeries ℂ)
    (hE'j : E' t = ModularCurve.qExpand ℂ M (ModularCurve.jqModC ℂ))
    (hE'Φ : ∀ u : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
        (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))),
        E' (Φ u) = ModularCurve.qExpand ℂ M (ModularCurve.coeffMap ι (u : LaurentSeries (AlgebraicClosure ℚ))))
    (y₀ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
        (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))))
    (hy₀ : (y₀ : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ)) (hΦy : Φ y₀ = t)
    (hΦfix : ∀ γ ∈ CongruenceSubgroup.Gamma1 M, ∀ u, σ γ (Φ u) = Φ u)
    (δ : SL(2, ℤ)) (hδ : ∀ u, σ δ (Φ u) = Φ u) :
    δ ∈ CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) := by sorry
