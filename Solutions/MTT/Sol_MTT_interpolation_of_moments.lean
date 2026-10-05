import Theorems.MTT.Thm_MTT_interpolation_conductor_one_of_moments
import Theorems.MTT.Thm_MTT_interpolation_positive_conductor_of_moments

noncomputable section
open scoped BigOperators

open MTT in
theorem solution
    {p N k : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (α : ℂ_[p]) (hα : IsOrdinaryRoot f ιp α)
    (μ : Bool → UnitMeasure p)
    (hμ : ∀ s, RealizesMoments f ιp P α s (μ s)) :
    Interpolates f ιp P.omega α (μ true + μ false) := by
  unfold Interpolates
  intro n χ hχ j hj
  cases n with
  | zero =>
      exact MTT.interpolation_conductor_one_of_moments
        hN hk ι ιp f P α hα μ hμ χ hχ j hj
  | succ n =>
      exact MTT.interpolation_positive_conductor_of_moments
        hN hk ι ιp f P α hα μ hμ (n + 1) (Nat.zero_lt_succ n) χ hχ j hj
