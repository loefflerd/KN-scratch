import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Linarith
set_option autoImplicit false

theorem MTT.coeff_eq_of_hecke_recurrence (k : ℕ) (e a b c : ℕ → ℂ)
    (hb : ∀ p : ℕ, p.Prime → ∀ m : ℕ,
      b (p * m) + e p * (p : ℂ) ^ (k - 1) * (if p ∣ m then b (m / p) else 0) = a p * b m)
    (hc : ∀ p : ℕ, p.Prime → ∀ m : ℕ,
      c (p * m) + e p * (p : ℂ) ^ (k - 1) * (if p ∣ m then c (m / p) else 0) = a p * c m)
    (hc1 : c 1 = 1) :
    ∀ m : ℕ, 0 < m → b m = b 1 * c m := by sorry
