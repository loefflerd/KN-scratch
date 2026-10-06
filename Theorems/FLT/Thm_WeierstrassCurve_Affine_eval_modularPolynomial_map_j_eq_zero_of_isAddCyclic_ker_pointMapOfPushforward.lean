import Definitions.FLT.Def_Isogeny_ConditionalCurrency
import Definitions.FLT.Def_ModularCurve_X0
import Definitions.FLT.Def_WeierstrassCurve_GenusOnePlaceGateCentred

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve
theorem WeierstrassCurve.Affine.eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward
    (K : Type) [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
    (E E' : WeierstrassCurve.Affine K) [E.IsElliptic] [E'.IsElliptic]
    [GenusOnePlaceGate E] [GenusOnePlaceGate.IsCentred E] [AbelTheorem E]
    [GenusOnePlaceGate E'] [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E']
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong K ι)
    (hN : NormFormulaAlong K ι hfin) (N : ℕ) [NeZero N]
    (hcyc : IsAddCyclic (pointMapOfPushforward ι hι hfin hN).ker)
    (hcard : Nat.card (pointMapOfPushforward ι hι hfin hN).ker = N)
    (data : ModularCurve.ModularPolynomialData N) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom K) E.j)).eval E'.j = 0 := by sorry
