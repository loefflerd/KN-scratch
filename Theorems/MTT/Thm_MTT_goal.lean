module

public import Definitions.MTT.Def_MTT_Measures

import Theorems.MTT.Thm_MTT_periods_exist
import Theorems.MTT.Thm_MTT_ordinary_root_exists_unique
import Theorems.MTT.Thm_MTT_measure_extension
import Theorems.MTT.Thm_MTT_interpolation_of_moments

/-!
# The ordinary p-adic L-function: assembling the interpolation theorem

The theorem `MTT.goal` constructs an ordinary root, a system of complex periods, and a
`ℂ_[p]`-valued measure on the p-adic units satisfying the interpolation property for a
normalized algebraic cuspidal eigenform of positive level and weight at least two.
The ordinarity hypothesis is that the image of its coefficient at `p` has p-adic norm one.

The proof combines the existence of the ordinary root and periods with the measure-extension
theorem for each sign. Adding the two signed measures gives the measure in the conclusion,
and the interpolation formula follows from the theorem relating interpolation to moments.
-/

section privateSection

noncomputable section
open scoped BigOperators
open MTT in
theorem solution
    {p N k : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (hord : ‖ιp (f.coeff p)‖ = 1) :
    ∃ (α : ℂ_[p]) (P : Periods k ι f.form) (μ : UnitMeasure p),
      IsOrdinaryRoot f ιp α ∧ Interpolates f ιp P.omega α μ := by
  obtain ⟨α, hα, _⟩ := ordinary_root_exists_unique hk ι ιp f hord
  obtain ⟨P⟩ := periods_exist hN hk ι f
  have hm : ∀ s, ∃ μ : UnitMeasure p, RealizesMoments f ιp P α s μ :=
    fun s => (measure_extension hN hk ι ιp f P α hα s).exists
  choose μ hμ using hm
  exact ⟨α, P, μ true + μ false, hα,
    interpolation_of_moments hN hk ι ιp f P α hα μ hμ⟩
end

end privateSection

public section publicSection

noncomputable section
open scoped BigOperators

open MTT in
theorem MTT.goal
    {p N k : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (hord : ‖ιp (f.coeff p)‖ = 1) :
    ∃ (α : ℂ_[p]) (P : Periods k ι f.form) (μ : UnitMeasure p),
      IsOrdinaryRoot f ιp α ∧ Interpolates f ιp P.omega α μ := _root_.solution hN hk ι ιp f hord
end

end publicSection
