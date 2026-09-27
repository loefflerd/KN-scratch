import Definitions.MTT.Def_MTT_Measures

set_option autoImplicit false
noncomputable section
open scoped BigOperators

open MTT in
theorem MTT.distribution_relation
    {p N k : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (α : ℂ_[p]) (hα : IsOrdinaryRoot f ιp α)
    (s : Bool) (j : ℕ) (hj : j ≤ k - 2) (n : ℕ) (hn : 0 < n) (a : ℤ) :
    (∑ b ∈ Finset.range p,
      diskMoment f ιp P α s j (n + 1) (a + (b : ℤ) * (p : ℤ) ^ n)) =
      diskMoment f ιp P α s j n a := by sorry
