import Mathlib
import Definitions.FLT.Def_ModularCurve_LevelNFunctionField

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
theorem ModularCurve.LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring N) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring N) K]
    [IsFractionRing (ModularCurve.LevelN.ring N) K] :
    ∃ (hst : ∀ γ : SL(2, ℤ), ∀ F ∈ ModularCurve.LevelN.ring N,
        (fun τ : UpperHalfPlane => F (γ • τ)) ∈ ModularCurve.LevelN.ring N)
      (σ : SL(2, ℤ) →* (K ≃ₐ[ℂ] K)),
      (∀ (γ : SL(2, ℤ)) (F : UpperHalfPlane → ℂ) (hF : F ∈ ModularCurve.LevelN.ring N),
          σ γ (algebraMap (ModularCurve.LevelN.ring N) K ⟨F, hF⟩) =
            algebraMap (ModularCurve.LevelN.ring N) K
              ⟨fun τ : UpperHalfPlane => F (γ⁻¹ • τ), hst γ⁻¹ F hF⟩) ∧
      σ.ker = CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) ∧
      IntermediateField.fixedField σ.range =
        IntermediateField.adjoin ℂ
          ({algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)} : Set K) ∧
      Transcendental ℂ (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)) ∧
      FiniteDimensional
          (IntermediateField.adjoin ℂ
            ({algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)} : Set K)) K ∧
      Module.finrank
          (IntermediateField.adjoin ℂ
            ({algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)} : Set K)) K =
        (CongruenceSubgroup.Gamma N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ∧
      IsGalois
          (IntermediateField.adjoin ℂ
            ({algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)} : Set K)) K := by sorry
