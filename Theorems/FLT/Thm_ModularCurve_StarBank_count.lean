import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial
theorem ModularCurve.StarBank.count {K : Type*} [Field K] [IsAlgClosed K] {p : ℕ}
    (hp0 : (p : K) ≠ 0) (hp2 : 2 ≤ p) {R G : Polynomial K} (hR : R.Monic)
    (hRdeg : R.natDegree = p) (hG : 0 < G.natDegree) {c : K} (hc : c ≠ 0)
    (hdvd : G.comp R ∣ Polynomial.C c * G ^ (p + 1)) :
    ∃ β₀ : K, (∀ β : K, G.IsRoot β → β = β₀) ∧
      R = (Polynomial.X - Polynomial.C β₀) ^ p + Polynomial.C β₀ := by sorry
