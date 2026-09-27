import Mathlib.NumberTheory.Padics.Complex
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Filter

theorem PadicMeasure.compatible_disk_values_vanish_of_decay {p : ℕ} [Fact p.Prime] (D : ℕ → ℤ → ℂ_[p])
    (hadd : ∀ n : ℕ, 0 < n → ∀ a : ℤ, IsCoprime a (p : ℤ) →
      (∑ b ∈ Finset.range p, D (n+1) (a+(b : ℤ)*(p : ℤ)^n)) = D n a)
    (B : ℕ → ℝ) (hB : Filter.Tendsto B Filter.atTop (nhds 0))
    (hbound : ∀ n : ℕ, 0 < n → ∀ a : ℤ, IsCoprime a (p : ℤ) → ‖D n a‖ ≤ B n) :
    ∀ n : ℕ, 0 < n → ∀ a : ℤ, IsCoprime a (p : ℤ) → D n a = 0 := by sorry
