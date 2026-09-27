import Mathlib
import Definitions.FLT.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.FLT.Def_WeierstrassCurve_OddOrderSummingSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve
theorem WeierstrassCurve.veluX_oddOrderSummingSet_injOn_psi2Sq_roots
    {L : Type*} [Field L] [DecidableEq L] (h2 : (2 : L) ≠ 0)
    (W : WeierstrassCurve L) [W.IsElliptic] (n : ℕ) (Q : W.toAffine.Point)
    (hQ : addOrderOf Q = 2 * n + 1) {r r' : L}
    (hr : W.Ψ₂Sq.eval r = 0) (hr' : W.Ψ₂Sq.eval r' = 0)
    (heq : W.veluX (W.oddOrderSummingSet Q n) r = W.veluX (W.oddOrderSummingSet Q n) r') :
    r = r' := by sorry
