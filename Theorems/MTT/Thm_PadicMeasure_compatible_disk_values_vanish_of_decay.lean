module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic

section privateSection

open scoped BigOperators
open Filter

lemma child_coprime {p n : ℕ} (hn : 0 < n) {a : ℤ}
    (ha : IsCoprime a p) (b : ℕ) :
    IsCoprime (a + b * p ^ n) p := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simpa [pow_succ, mul_assoc] using ha.add_mul_right_left (b * (p : ℤ) ^ m)

/-- Compatible residue-disk values that decay uniformly with depth vanish. -/
theorem solution {p : ℕ} [Fact p.Prime] (D : ℕ → ℤ → ℂ_[p])
    (hadd : ∀ n : ℕ, 0 < n → ∀ a : ℤ, IsCoprime a (p : ℤ) →
      (∑ b ∈ Finset.range p, D (n+1) (a+(b : ℤ)*(p : ℤ)^n)) = D n a)
    (B : ℕ → ℝ) (hB : Filter.Tendsto B Filter.atTop (nhds 0))
    (hbound : ∀ n : ℕ, 0 < n → ∀ a : ℤ, IsCoprime a (p : ℤ) → ‖D n a‖ ≤ B n) :
    ∀ n : ℕ, 0 < n → ∀ a : ℤ, IsCoprime a (p : ℤ) → D n a = 0 := by
  have hiter : ∀ r n : ℕ, 0 < n → ∀ a : ℤ, IsCoprime a (p : ℤ) →
      ‖D n a‖ ≤ B (n+r) := by
    intro r
    induction r with
    | zero => simpa using hbound
    | succ r ih =>
      intro n hn a ha
      rw [← hadd n hn a ha]
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonempty
        (Finset.nonempty_range_iff.mpr (Fact.out : p.Prime).ne_zero)
      intro b _
      simpa only [Nat.add_assoc,Nat.add_comm 1] using
        ih (n+1) (by omega) (a+(b : ℤ)*(p : ℤ)^n) (child_coprime hn ha b)
  intro n hn a ha
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  have ht : Filter.Tendsto (fun r : ℕ => B (n+r)) Filter.atTop (nhds 0) :=
    hB.comp (by simpa only [Nat.add_comm] using tendsto_add_atTop_nat n)
  exact ge_of_tendsto ht (Filter.Eventually.of_forall (fun r => hiter r n hn a ha))

end privateSection

public noncomputable section publicSection
open scoped BigOperators
open Filter

theorem PadicMeasure.compatible_disk_values_vanish_of_decay {p : ℕ} [Fact p.Prime] (D : ℕ → ℤ → ℂ_[p])
    (hadd : ∀ n : ℕ, 0 < n → ∀ a : ℤ, IsCoprime a (p : ℤ) →
      (∑ b ∈ Finset.range p, D (n+1) (a+(b : ℤ)*(p : ℤ)^n)) = D n a)
    (B : ℕ → ℝ) (hB : Filter.Tendsto B Filter.atTop (nhds 0))
    (hbound : ∀ n : ℕ, 0 < n → ∀ a : ℤ, IsCoprime a (p : ℤ) → ‖D n a‖ ≤ B n) :
    ∀ n : ℕ, 0 < n → ∀ a : ℤ, IsCoprime a (p : ℤ) → D n a = 0 :=
  solution D hadd B hB hbound

end publicSection
