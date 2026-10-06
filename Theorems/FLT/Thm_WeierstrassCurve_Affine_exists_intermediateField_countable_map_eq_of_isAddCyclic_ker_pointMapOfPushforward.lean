import Definitions.FLT.Def_Isogeny_ConditionalCurrency
import Definitions.FLT.Def_WeierstrassCurve_GenusOnePlaceGateCentred

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u
theorem WeierstrassCurve.Affine.exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward
    {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
    (E E' : WeierstrassCurve.Affine K) [E.IsElliptic] [E'.IsElliptic]
    [GenusOnePlaceGate E] [GenusOnePlaceGate.IsCentred E] [AbelTheorem E]
    [GenusOnePlaceGate E'] [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E']
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong K ι)
    (hN : NormFormulaAlong K ι hfin) (N : ℕ) [NeZero N]
    (hcyc : IsAddCyclic (pointMapOfPushforward ι hι hfin hN).ker)
    (hcard : Nat.card (pointMapOfPushforward ι hι hfin hN).ker = N) :
    letI : Algebra ℚ K := DivisionRing.toRatAlgebra
    ∃ (K₀ : IntermediateField ℚ K) (_ : Countable K₀)
      (E₀ E₀' : WeierstrassCurve K₀) (_ : E₀.IsElliptic) (_ : E₀'.IsElliptic)
      (_ : E₀.map (algebraMap K₀ K) = E) (_ : E₀'.map (algebraMap K₀ K) = E')
      (_ : (E₀.baseChange (AlgebraicClosure K₀)).IsElliptic)
      (_ : (E₀'.baseChange (AlgebraicClosure K₀)).IsElliptic)
      (ι₀ : (E₀'.baseChange (AlgebraicClosure K₀)).toAffine.FunctionField →ₐ[AlgebraicClosure K₀]
        (E₀.baseChange (AlgebraicClosure K₀)).toAffine.FunctionField)
      (hι₀ : ι₀.toRingHom.IsIntegral) (hfin₀ : FiniteAlong (AlgebraicClosure K₀) ι₀),
      ∀ [DecidableEq (AlgebraicClosure K₀)]
        [GenusOnePlaceGate (E₀.baseChange (AlgebraicClosure K₀)).toAffine]
        [GenusOnePlaceGate.IsCentred (E₀.baseChange (AlgebraicClosure K₀)).toAffine]
        [AbelTheorem (E₀.baseChange (AlgebraicClosure K₀)).toAffine]
        [GenusOnePlaceGate (E₀'.baseChange (AlgebraicClosure K₀)).toAffine]
        [GenusOnePlaceGate.IsCentred (E₀'.baseChange (AlgebraicClosure K₀)).toAffine]
        [AbelTheorem (E₀'.baseChange (AlgebraicClosure K₀)).toAffine]
        (hN₀ : NormFormulaAlong (AlgebraicClosure K₀) ι₀ hfin₀),
        IsAddCyclic (pointMapOfPushforward ι₀ hι₀ hfin₀ hN₀).ker ∧
          Nat.card (pointMapOfPushforward ι₀ hι₀ hfin₀ hN₀).ker = N := by sorry
