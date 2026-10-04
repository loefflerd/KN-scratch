import Definitions.FLT.Def_AlgebraicCurve_RegularDifferentials
import Definitions.FLT.Def_ModularCurve_LevelNFunctionField

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold
theorem ModularCurve.LevelN.exists_linearMap_regularDifferentials_mdifferentiable
    (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring N) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring N) K]
    [IsFractionRing (ModularCurve.LevelN.ring N) K] :
    (∀ ω ∈ AlgebraicCurve.regularDifferentials ℂ K,
      ∃ (a b c e : UpperHalfPlane → ℂ) (ha : a ∈ ModularCurve.LevelN.ring N)
        (hb : b ∈ ModularCurve.LevelN.ring N) (hc : c ∈ ModularCurve.LevelN.ring N)
        (he : e ∈ ModularCurve.LevelN.ring N), b ≠ 0 ∧ e ≠ 0 ∧
        ω = (algebraMap (ModularCurve.LevelN.ring N) K ⟨a, ha⟩ /
              algebraMap (ModularCurve.LevelN.ring N) K ⟨b, hb⟩) •
            KaehlerDifferential.D ℂ K (algebraMap (ModularCurve.LevelN.ring N) K ⟨c, hc⟩ /
              algebraMap (ModularCurve.LevelN.ring N) K ⟨e, he⟩)) ∧
    ∃ Ψ : AlgebraicCurve.regularDifferentials ℂ K →ₗ[ℂ] (UpperHalfPlane → ℂ),
      Function.Injective Ψ ∧
      (∀ ω, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Ψ ω)) ∧
      ∀ (ω : AlgebraicCurve.regularDifferentials ℂ K) (a b c e : UpperHalfPlane → ℂ)
        (ha : a ∈ ModularCurve.LevelN.ring N) (hb : b ∈ ModularCurve.LevelN.ring N)
        (hc : c ∈ ModularCurve.LevelN.ring N) (he : e ∈ ModularCurve.LevelN.ring N),
        b ≠ 0 → e ≠ 0 →
        (ω : KaehlerDifferential ℂ K) =
          (algebraMap (ModularCurve.LevelN.ring N) K ⟨a, ha⟩ /
              algebraMap (ModularCurve.LevelN.ring N) K ⟨b, hb⟩) •
            KaehlerDifferential.D ℂ K (algebraMap (ModularCurve.LevelN.ring N) K ⟨c, hc⟩ /
              algebraMap (ModularCurve.LevelN.ring N) K ⟨e, he⟩) →
        ∀ τ : UpperHalfPlane, Ψ ω τ * b τ * e τ ^ 2 =
          a τ * (e τ * deriv (c ∘ UpperHalfPlane.ofComplex) τ -
            c τ * deriv (e ∘ UpperHalfPlane.ofComplex) τ) := by sorry
