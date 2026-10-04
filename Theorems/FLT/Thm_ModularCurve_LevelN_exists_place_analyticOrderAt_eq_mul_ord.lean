import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.FLT.Def_ModularCurve_LevelNFunctionField

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups
theorem ModularCurve.LevelN.exists_place_analyticOrderAt_eq_mul_ord (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring N) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring N) K]
    [IsFractionRing (ModularCurve.LevelN.ring N) K] (τ₀ : UpperHalfPlane) :
    ∃ (W : AlgebraicCurve.Place ℂ K) (e : ℕ), 0 < e ∧
      ∀ (F : UpperHalfPlane → ℂ) (hF : F ∈ ModularCurve.LevelN.ring N), F ≠ 0 →
        analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (τ₀ : ℂ) ≠ ⊤ ∧
        ((analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (τ₀ : ℂ)).toNat : ℤ) =
          e * W.ord (algebraMap (ModularCurve.LevelN.ring N) K ⟨F, hF⟩) := by sorry
