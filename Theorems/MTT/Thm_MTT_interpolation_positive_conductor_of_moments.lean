import Definitions.MTT.Def_MTT_Measures

noncomputable section
open scoped BigOperators

open MTT in
theorem MTT.interpolation_positive_conductor_of_moments
    {p N k : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (α : ℂ_[p]) (hα : IsOrdinaryRoot f ιp α)
    (μ : Bool → UnitMeasure p)
    (hμ : ∀ s, RealizesMoments f ιp P α s (μ s))
    (n : ℕ) (hn : 0 < n) (χ : DirichletCharacter Qbar (p ^ n))
    (hχ : χ.IsPrimitive) (j : ℕ) (hj : j ≤ k - 2) :
    ∃ (g : C((ℤ_[p])ˣ, ℂ_[p])) (v : Qbar),
      (∀ x, g x = specialFunction ιp n χ j x) ∧
      ι v = normalizedCriticalValue f P.omega n χ j ∧
      (μ true + μ false) g = eulerMultiplier f ιp α n χ j * ιp v := by sorry
