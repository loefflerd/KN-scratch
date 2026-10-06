import Definitions.FLT.Def_Isogeny_ConditionalCurrency
import Definitions.FLT.Def_WeierstrassCurve_GenusOnePlaceGateCentred

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve
theorem WeierstrassCurve.Affine.exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward
    (R₀ : Type) [Field R₀] (E₀ E₀' : WeierstrassCurve R₀) [E₀.IsElliptic] [E₀'.IsElliptic]
    (F F' : Type) [Field F] [Field F'] [Algebra R₀ F] [Algebra R₀ F']
    [DecidableEq F] [DecidableEq F'] [IsAlgClosed F] [IsAlgClosed F'] [CharZero F] [CharZero F']
    [(E₀.baseChange F).IsElliptic] [(E₀'.baseChange F).IsElliptic]
    [(E₀.baseChange F').IsElliptic] [(E₀'.baseChange F').IsElliptic]
    [GenusOnePlaceGate (E₀.baseChange F).toAffine] [GenusOnePlaceGate.IsCentred (E₀.baseChange F).toAffine]
    [AbelTheorem (E₀.baseChange F).toAffine]
    [GenusOnePlaceGate (E₀'.baseChange F).toAffine] [GenusOnePlaceGate.IsCentred (E₀'.baseChange F).toAffine]
    [AbelTheorem (E₀'.baseChange F).toAffine]
    [GenusOnePlaceGate (E₀.baseChange F').toAffine] [GenusOnePlaceGate.IsCentred (E₀.baseChange F').toAffine]
    [AbelTheorem (E₀.baseChange F').toAffine]
    [GenusOnePlaceGate (E₀'.baseChange F').toAffine] [GenusOnePlaceGate.IsCentred (E₀'.baseChange F').toAffine]
    [AbelTheorem (E₀'.baseChange F').toAffine]
    (σ : F →ₐ[R₀] F')
    (ι₀ : (E₀'.baseChange F).toAffine.FunctionField →ₐ[F] (E₀.baseChange F).toAffine.FunctionField)
    (hι₀ : ι₀.toRingHom.IsIntegral) (hfin₀ : FiniteAlong F ι₀) (hN₀ : NormFormulaAlong F ι₀ hfin₀)
    (N : ℕ) [NeZero N]
    (hcyc : IsAddCyclic (pointMapOfPushforward ι₀ hι₀ hfin₀ hN₀).ker)
    (hcard : Nat.card (pointMapOfPushforward ι₀ hι₀ hfin₀ hN₀).ker = N) :
    ∃ (ι₁ : (E₀'.baseChange F').toAffine.FunctionField →ₐ[F'] (E₀.baseChange F').toAffine.FunctionField)
      (hι₁ : ι₁.toRingHom.IsIntegral) (hfin₁ : FiniteAlong F' ι₁),
      ∀ hN₁ : NormFormulaAlong F' ι₁ hfin₁,
        IsAddCyclic (pointMapOfPushforward ι₁ hι₁ hfin₁ hN₁).ker ∧
          Nat.card (pointMapOfPushforward ι₁ hι₁ hfin₁ hN₁).ker = N := by sorry
