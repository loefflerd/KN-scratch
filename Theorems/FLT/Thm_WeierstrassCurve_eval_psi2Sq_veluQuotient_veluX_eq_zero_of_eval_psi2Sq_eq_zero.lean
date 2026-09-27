import Mathlib
import Definitions.FLT.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.FLT.Def_WeierstrassCurve_OddOrderSummingSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve
theorem WeierstrassCurve.eval_psi2Sq_veluQuotient_veluX_eq_zero_of_eval_psi2Sq_eq_zero
    {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L] (h2 : (2 : L) ≠ 0)
    (W : WeierstrassCurve L) [W.IsElliptic] (n : ℕ) (Q : W.toAffine.Point)
    (hQ : addOrderOf Q = 2 * n + 1) {r : L} (hr : W.Ψ₂Sq.eval r = 0) :
    (W.veluQuotient (W.oddOrderSummingSet Q n)).Ψ₂Sq.eval
      (W.veluX (W.oddOrderSummingSet Q n) r) = 0 := by sorry
