import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.Measure.Basic

set_option autoImplicit false
noncomputable section
open scoped BigOperators


theorem PadicMeasure.colmez_r0_moment_extension
    {p : ℕ} [Fact p.Prime] (d : ℕ)
    (M : ℕ → ℕ → ℤ → ℂ_[p])
    (hres : ∀ (n : ℕ), 0 < n → ∀ (a b : ℤ),
      IsCoprime a (p : ℤ) → IsCoprime b (p : ℤ) →
      (a : ZMod (p^n)) = (b : ZMod (p^n)) → M 0 n a = M 0 n b)
    (hadd : ∀ (j : ℕ), j ≤ d → ∀ (n : ℕ), 0 < n →
      ∀ (a : ℤ), IsCoprime a (p : ℤ) →
        (∑ b ∈ Finset.range p, M j (n+1) (a+(b : ℤ)*(p : ℤ)^n)) = M j n a)
    (hbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 0 < n →
      ∀ (a : ℤ), IsCoprime a (p : ℤ) → ∀ (j : ℕ), j ≤ d →
        ‖∑ t ∈ Finset.range (j+1),
          (j.choose t : ℂ_[p]) * (-(a : ℂ_[p]))^(j-t) * M t n a‖ ≤
          C * ‖(p : ℂ_[p])^(n*j)‖) :
    ∃! μ : AbstractMeasure (ℤ_[p])ˣ ℂ_[p] ℂ_[p],
      ∀ (n : ℕ), 0 < n → ∀ (a : ℤ), IsCoprime a (p : ℤ) →
        ∀ (j : ℕ), j ≤ d → ∃ g : C((ℤ_[p])ˣ, ℂ_[p]),
          (∀ x, g x = if PadicInt.toZModPow n x.val = (a : ZMod (p^n))
            then (algebraMap ℚ_[p] ℂ_[p] (x.val : ℚ_[p]))^j else 0) ∧
          μ g = M j n a := by sorry

