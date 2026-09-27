import Mathlib
import Definitions.FLT.Def_AlgebraicCurve_Correspondence
import Definitions.FLT.Def_AlgebraicCurve_BaseChangeGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
open scoped IntermediateField

universe u v in
theorem AlgebraicCurve.Place.ord_restrictAlong_eq_natCard_algHom_of_isGalois
    (K : Type u) [Field K] [IsAlgClosed K]
    {F M : Type v} [Field F] [Field M] [Algebra K F] [Algebra K M]
    (x : F) (t : M) (j₀ : K) (ι : F →ₐ[K] M) (hι : ι x = t)
    (hfin : FiniteDimensional K⟮t⟯ M) (hgal : IsGalois K⟮t⟯ M)
    (hint : ∀ ψ : F →ₐ[K] M, ψ x = t → ψ.toRingHom.IsIntegral)
    (W₀ : Place K M) (hW₀ : 0 < W₀.ord (t - algebraMap K M j₀)) :
    (W₀.ord (t - algebraMap K M j₀) =
        Nat.card {σ : M ≃ₐ[K⟮t⟯] M // SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀}) ∧
    (∀ (ψ : F →ₐ[K] M) (hψ : ψ x = t),
        0 < (W₀.restrictAlong ψ (hint ψ hψ)).ord (x - algebraMap K F j₀)) ∧
    (∀ w : Place K F, 0 < w.ord (x - algebraMap K F j₀) →
        ∃ (ψ : F →ₐ[K] M) (hψ : ψ x = t), W₀.restrictAlong ψ (hint ψ hψ) = w) ∧
    (∀ (ψ ψ' : F →ₐ[K] M) (hψ : ψ x = t) (hψ' : ψ' x = t),
        W₀.restrictAlong ψ (hint ψ hψ) = W₀.restrictAlong ψ' (hint ψ' hψ') ↔
          ∃ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ ∧
            ψ' = ((σ : M →ₐ[K⟮t⟯] M).restrictScalars K).comp ψ) ∧
    (∀ (ψ : F →ₐ[K] M) (hψ : ψ x = t),
        (W₀.restrictAlong ψ (hint ψ hψ)).ord (x - algebraMap K F j₀) =
          Nat.card {ψ' : {ψ' : F →ₐ[K] M // ψ' x = t} //
            W₀.restrictAlong ψ'.1 (hint ψ'.1 ψ'.2) = W₀.restrictAlong ψ (hint ψ hψ)}) := by sorry
