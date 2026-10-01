import Definitions.FLT.Def_ModularCurve_ModuliPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve WeierstrassCurve WeierstrassCurve.Affine
theorem ModularCurve.natCard_moduliPoint_j_eq_eq_natCard_quot_addOrderOf_eq
    (N : ℕ) (L : Type*) [Field L] [DecidableEq L] [IsAlgClosed L]
    (W : WeierstrassCurve L) [W.IsElliptic] :
    Nat.card {x : ModuliPoint N L // ModuliPoint.j x = W.j}
      = Nat.card (Quot (fun (T T' : {T : W.toAffine.Point // addOrderOf T = N}) =>
          ∃ γ : VariableChange L, ∃ _ : γ • W = W, ∃ k : ℕ, k.Coprime N ∧
            HEq T'.1 (k • Point.vcInvFun γ W.toAffine T.1))) := by sorry
