import Definitions.MTT.Def_MTT_Measures

noncomputable section
open scoped BigOperators

open MTT in
theorem MTT.goal
    {p N k : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (hord : ‖ιp (f.coeff p)‖ = 1) :
    ∃ (α : ℂ_[p]) (P : Periods k ι f.form) (μ : UnitMeasure p),
      IsOrdinaryRoot f ιp α ∧ Interpolates f ιp P.omega α μ := by
  sorry
