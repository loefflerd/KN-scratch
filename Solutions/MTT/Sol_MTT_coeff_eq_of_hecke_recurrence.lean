import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Linarith
set_option autoImplicit false

theorem solution (k : ℕ) (e a b c : ℕ → ℂ)
    (hb : ∀ p : ℕ, p.Prime → ∀ m : ℕ,
      b (p * m) + e p * (p : ℂ) ^ (k - 1) * (if p ∣ m then b (m / p) else 0) = a p * b m)
    (hc : ∀ p : ℕ, p.Prime → ∀ m : ℕ,
      c (p * m) + e p * (p : ℂ) ^ (k - 1) * (if p ∣ m then c (m / p) else 0) = a p * c m)
    (hc1 : c 1 = 1) :
    ∀ m : ℕ, 0 < m → b m = b 1 * c m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm
  rcases Nat.lt_or_ge m 2 with h2 | h2
  · have : m = 1 := by omega
    subst this; simp [hc1]
  · obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (show m ≠ 1 by omega)
    obtain ⟨m', rfl⟩ := hpm
    have hm' : 0 < m' := by
      rcases Nat.eq_zero_or_pos m' with h | h
      · subst h; simp at hm
      · exact h
    have hlt : m' < p * m' := (Nat.lt_mul_iff_one_lt_left hm').mpr hp.one_lt
    have ihm' := ih m' hlt hm'
    have key_b := hb p hp m'
    have key_c := hc p hp m'
    -- the corrective term
    have hcorr : (if p ∣ m' then b (m' / p) else 0) = b 1 * (if p ∣ m' then c (m' / p) else 0) := by
      split_ifs with hd
      · have hpos : 0 < m' / p := Nat.div_pos (Nat.le_of_dvd hm' hd) hp.pos
        have hlt' : m' / p < p * m' := lt_of_le_of_lt (Nat.div_le_self _ _) hlt
        exact ih _ hlt' hpos
      · simp
    have : b (p * m') = a p * b m' - e p * (p : ℂ) ^ (k - 1) * (if p ∣ m' then b (m' / p) else 0) := by
      rw [← key_b]; ring
    rw [this, ihm', hcorr]
    have : c (p * m') = a p * c m' - e p * (p : ℂ) ^ (k - 1) * (if p ∣ m' then c (m' / p) else 0) := by
      rw [← key_c]; ring
    rw [this]; ring

