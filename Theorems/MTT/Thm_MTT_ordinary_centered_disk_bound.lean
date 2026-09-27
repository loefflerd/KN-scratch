import Definitions.MTT.Def_MTT_Measures

set_option autoImplicit false
noncomputable section
open scoped BigOperators

open MTT in
theorem MTT.ordinary_centered_disk_bound
    {p N k : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (α : ℂ_[p]) (hα : IsOrdinaryRoot f ιp α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Bool) (n : ℕ), 0 < n →
      ∀ (a : ℤ) (j : ℕ), j ≤ k - 2 →
        ‖∑ t ∈ Finset.range (j + 1),
          (j.choose t : ℂ_[p]) * (-(a : ℂ_[p])) ^ (j - t) *
            diskMoment f ιp P α s t n a‖ ≤
          C * ‖(p : ℂ_[p]) ^ (n * j)‖ := by sorry

