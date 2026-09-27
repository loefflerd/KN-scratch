import Theorems.MTT.Thm_MTT_periods_exist
import Theorems.MTT.Thm_MTT_ordinary_root_exists_unique
import Theorems.MTT.Thm_MTT_measure_extension
import Theorems.MTT.Thm_MTT_interpolation_of_moments

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MTT in
theorem solution
    {p N k : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (hord : ‖ιp (f.coeff p)‖ = 1) :
    ∃ (α : ℂ_[p]) (P : Periods k ι f.form) (μ : UnitMeasure p),
      IsOrdinaryRoot f ιp α ∧ Interpolates f ιp P.omega α μ := by
  obtain ⟨α, hα, _⟩ := ordinary_root_exists_unique hN hk ι ιp f hord
  obtain ⟨P⟩ := periods_exist hN hk ι f
  have hm : ∀ s, ∃ μ : UnitMeasure p, RealizesMoments f ιp P α s μ :=
    fun s => (measure_extension hN hk ι ιp f P α hα s).exists
  choose μ hμ using hm
  exact ⟨α, P, μ true + μ false, hα,
    interpolation_of_moments hN hk ι ιp f P α hα μ hμ⟩
