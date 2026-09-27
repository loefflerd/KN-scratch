import Definitions.MTT.Def_MTT_Measures
open MTT
open scoped BigOperators
theorem MTT.character_integral_of_disk_moments {p N k : ℕ} [Fact p.Prime]
    {ι : Qbar →+* ℂ} (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (α : ℂ_[p]) (s : Bool) (μ : UnitMeasure p)
    (hμ : RealizesMoments f ιp P α s μ)
    (n : ℕ) (hn : 0 < n) (χ : DirichletCharacter Qbar (p ^ n))
    (j : ℕ) (hj : j ≤ k - 2) :
    ∃ g : C((ℤ_[p])ˣ, ℂ_[p]),
      (∀ x, g x = specialFunction ιp n χ j x) ∧
      μ g = ∑ a : (ZMod (p ^ n))ˣ,
        ιp (χ a) * diskMoment f ιp P α s j n ((a : ZMod (p ^ n)).val : ℤ) := by sorry
