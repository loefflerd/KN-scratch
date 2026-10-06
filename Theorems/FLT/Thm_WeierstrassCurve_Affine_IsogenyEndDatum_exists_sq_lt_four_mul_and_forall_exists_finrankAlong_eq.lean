import Definitions.FLT.Def_Isogeny_ConditionalCurrency
import Definitions.FLT.Def_WeierstrassCurve_GenusOnePlaceGateCentred

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u
theorem WeierstrassCurve.Affine.IsogenyEndDatum.exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic] [GenusOnePlaceGate W] [AbelTheorem W]
    [GenusOnePlaceGate.IsCentred W]
    (hNs : ∀ D : IsogenyEndDatum W, NormFormulaAlong F D.ι D.hfin)
    (D₀ : IsogenyEndDatum W) (hD₀ : ¬ ∃ m : ℤ, ∀ P : W.Point, D₀.pointEnd (hNs D₀) P = m • P) :
    ∃ t n : ℤ, t ^ 2 < 4 * n ∧
      ∀ a b : ℤ, b ≠ 0 → ∃ D : IsogenyEndDatum W,
        (finrankAlong F D.ι : ℤ) = a ^ 2 + t * a * b + n * b ^ 2 := by sorry
