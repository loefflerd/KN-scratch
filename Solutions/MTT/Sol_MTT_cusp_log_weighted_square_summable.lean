import Definitions.MTT.Def_MTT_Cohomology_Boundary
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries

/-!
# Log-weighted square summability of the Fourier coefficients of a cusp form

For a cusp form `f` of weight `k ≥ 2` on `Γ₁(N)` with width-one Fourier coefficients `a n`, we
prove
`∑ n, ‖a n‖ ^ 2 * log n / n ^ (k + 1) < ∞`.

The argument follows Rudnick, *Modular forms 2019: Petersson's formula*, §1: Hecke's pointwise
bound `y ^ k * ‖f (x + i y)‖ ^ 2 ≤ C` (Lemma 1.1(b), available in Mathlib as
`CuspFormClass.exists_bound`) together with Parseval's identity on the horizontal line
`Im τ = 1 / n` gives the mean-square estimate `∑_{m < n} ‖a m‖ ^ 2 ≤ D * n ^ k` (the inequality
(1) in the proof of Theorem 1.2); dyadic summation then yields the stated convergence.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MTT.Cohomology

open UpperHalfPlane hiding I
open Complex Finset MeasureTheory
open scoped Real ModularForm MatrixGroups Manifold Topology

namespace MTT

/-! ### Dyadic summation -/

/-- The partial sums of `∑ (j + 1) / 2 ^ j` are bounded by `4`. -/
theorem sum_range_succ_div_two_pow_le (J : ℕ) :
    ∑ j ∈ range J, ((j : ℝ) + 1) / 2 ^ j ≤ 4 := by
  -- closed form `4 - 2 (J + 2) / 2 ^ J`, then drop the nonnegative correction term
  have h : ∀ J : ℕ, ∑ j ∈ range J, ((j : ℝ) + 1) / 2 ^ j = 4 - 2 * ((J : ℝ) + 2) / 2 ^ J := by
    intro J
    induction J with
    | zero => norm_num
    | succ J ih => rw [Finset.sum_range_succ, ih]; push_cast; field_simp; ring
  rw [h]
  have : 0 ≤ 2 * ((J : ℝ) + 2) / 2 ^ J := by positivity
  linarith

/-- `log n ≤ (j + 1) * log 2` whenever `n < 2 ^ (j + 1)`. -/
theorem log_le_succ_mul_log_two_of_lt_two_pow {n j : ℕ} (hn : n < 2 ^ (j + 1)) :
    Real.log n ≤ ((j : ℝ) + 1) * Real.log 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp only [Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (by positivity) (Real.log_nonneg one_le_two)
  · calc Real.log n ≤ Real.log ((2 : ℝ) ^ (j + 1)) :=
          Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast hn.le)
      _ = ((j : ℝ) + 1) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring

/-- Dyadic block bound: if the partial sums of a nonnegative sequence `b` are at most
`D * M ^ k`, the block of `b n * log n / n ^ (k + 1)` over `[2 ^ j, 2 ^ (j + 1))` is at most
`D * 2 ^ k * log 2 * (j + 1) / 2 ^ j`. -/
theorem sum_Ico_two_pow_mul_log_div_pow_le {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) {k : ℕ} {D : ℝ}
    (hS : ∀ M : ℕ, ∑ n ∈ range M, b n ≤ D * (M : ℝ) ^ k) (j : ℕ) :
    ∑ n ∈ Ico (2 ^ j) (2 ^ (j + 1)), b n * Real.log n / (n : ℝ) ^ (k + 1) ≤
      D * 2 ^ k * Real.log 2 * (((j : ℝ) + 1) / 2 ^ j) := by
  -- on the block, `log n ≤ (j + 1) log 2` and `n ^ (k + 1) ≥ 2 ^ (j (k + 1))`
  have hW0 : 0 ≤ ((j : ℝ) + 1) * Real.log 2 / 2 ^ (j * (k + 1)) :=
    div_nonneg (mul_nonneg (by positivity) (Real.log_nonneg one_le_two)) (by positivity)
  have hterm : ∀ n ∈ Ico (2 ^ j) (2 ^ (j + 1)), b n * Real.log n / (n : ℝ) ^ (k + 1) ≤
      b n * (((j : ℝ) + 1) * Real.log 2 / 2 ^ (j * (k + 1))) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le (Nat.two_pow_pos j) hn.1
    have h2j : (2 : ℝ) ^ (j * (k + 1)) ≤ (n : ℝ) ^ (k + 1) := by
      rw [pow_mul]
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hn.1) _
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hb n)
    exact div_le_div₀ (mul_nonneg (by positivity) (Real.log_nonneg one_le_two))
      (log_le_succ_mul_log_two_of_lt_two_pow hn.2) (by positivity) h2j
  calc ∑ n ∈ Ico (2 ^ j) (2 ^ (j + 1)), b n * Real.log n / (n : ℝ) ^ (k + 1)
      ≤ ∑ n ∈ Ico (2 ^ j) (2 ^ (j + 1)),
          b n * (((j : ℝ) + 1) * Real.log 2 / 2 ^ (j * (k + 1))) := Finset.sum_le_sum hterm
    _ = (∑ n ∈ Ico (2 ^ j) (2 ^ (j + 1)), b n) *
          (((j : ℝ) + 1) * Real.log 2 / 2 ^ (j * (k + 1))) := by rw [Finset.sum_mul]
    _ ≤ (∑ n ∈ range (2 ^ (j + 1)), b n) *
          (((j : ℝ) + 1) * Real.log 2 / 2 ^ (j * (k + 1))) := by
        refine mul_le_mul_of_nonneg_right ?_ hW0
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (fun n hn ↦ Finset.mem_range.2 (Finset.mem_Ico.1 hn).2) (fun n _ _ ↦ hb n)
    _ ≤ D * ((2 ^ (j + 1) : ℕ) : ℝ) ^ k *
          (((j : ℝ) + 1) * Real.log 2 / 2 ^ (j * (k + 1))) :=
        mul_le_mul_of_nonneg_right (hS _) hW0
    _ = D * 2 ^ k * Real.log 2 * (((j : ℝ) + 1) / 2 ^ j) := by
        push_cast
        field_simp
        ring

/-- The partial sums over `range (2 ^ J)` of `b n * log n / n ^ (k + 1)` are uniformly bounded
when the partial sums of `b` are at most `D * M ^ k`. -/
theorem sum_range_two_pow_mul_log_div_pow_le {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) {k : ℕ} {D : ℝ}
    (hS : ∀ M : ℕ, ∑ n ∈ range M, b n ≤ D * (M : ℝ) ^ k) (J : ℕ) :
    ∑ n ∈ range (2 ^ J), b n * Real.log n / (n : ℝ) ^ (k + 1) ≤
      D * 2 ^ k * Real.log 2 * 4 := by
  have hD : 0 ≤ D := by
    have := hS 1
    simp at this
    linarith [hb 0]
  have hC : 0 ≤ D * 2 ^ k * Real.log 2 :=
    mul_nonneg (by positivity) (Real.log_nonneg one_le_two)
  -- strengthened bound with the partial geometric sum, by induction on `J`
  have key : ∀ J : ℕ, ∑ n ∈ range (2 ^ J), b n * Real.log n / (n : ℝ) ^ (k + 1) ≤
      D * 2 ^ k * Real.log 2 * ∑ j ∈ range J, ((j : ℝ) + 1) / 2 ^ j := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
      rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le _)
        (Nat.pow_le_pow_right two_pos (Nat.le_succ J)), ← Finset.range_eq_Ico,
        Finset.sum_range_succ, mul_add]
      exact add_le_add ih (sum_Ico_two_pow_mul_log_div_pow_le hb hS J)
  exact (key J).trans (mul_le_mul_of_nonneg_left (sum_range_succ_div_two_pow_le J) hC)

/-- **Dyadic summation.** If the partial sums of a nonnegative sequence `b` grow at most like
`D * M ^ k`, then `∑ b n * log n / n ^ (k + 1)` converges. -/
theorem summable_mul_log_div_pow_of_sum_range_le {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) {k : ℕ}
    {D : ℝ} (hS : ∀ M : ℕ, ∑ n ∈ range M, b n ≤ D * (M : ℝ) ^ k) :
    Summable (fun n : ℕ ↦ b n * Real.log n / (n : ℝ) ^ (k + 1)) := by
  have hnonneg : ∀ n : ℕ, 0 ≤ b n * Real.log n / (n : ℝ) ^ (k + 1) := fun n ↦
    div_nonneg (mul_nonneg (hb n) (Real.log_natCast_nonneg n)) (by positivity)
  refine summable_of_sum_range_le (c := D * 2 ^ k * Real.log 2 * 4) hnonneg fun M ↦ ?_
  calc ∑ n ∈ range M, b n * Real.log n / (n : ℝ) ^ (k + 1)
      ≤ ∑ n ∈ range (2 ^ M), b n * Real.log n / (n : ℝ) ^ (k + 1) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (Nat.lt_two_pow_self (n := M)).le) (fun n _ _ ↦ hnonneg n)
    _ ≤ D * 2 ^ k * Real.log 2 * 4 := sum_range_two_pow_mul_log_div_pow_le hb hS M

/-! ### Parseval on a horizontal line -/

/-- A continuous function on `ℝ` is square-integrable on any bounded interval `Ioc a b`. -/
theorem memLp_two_restrict_Ioc_of_continuous {g : ℝ → ℂ} (hg : Continuous g) (a b : ℝ) :
    MemLp g 2 (volume.restrict (Set.Ioc a b)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg.continuousOn (s := Set.Icc a b))
  exact MemLp.of_bound hg.aestronglyMeasurable C
    (ae_restrict_of_forall_mem measurableSet_Ioc fun x hx ↦ hC x (Set.Ioc_subset_Icc_self hx))

/-- The `n`-th `q`-expansion coefficient of a `1`-periodic function is `exp (2 π n y)` times the
`n`-th Fourier coefficient of its restriction to the horizontal line `Im τ = y`. -/
theorem qExpansion_coeff_eq_exp_mul_fourierCoeffOn {f : ℍ → ℂ}
    (hfper : Function.Periodic (f ∘ ofComplex) 1) (hfhol : MDiff f)
    (hfbdd : IsBoundedAtImInfty f) {y : ℝ} (hy : 0 < y) (n : ℕ) :
    (qExpansion 1 f).coeff n = Real.exp (2 * π * n * y) *
      fourierCoeffOn zero_lt_one (fun x : ℝ ↦ f ⟨x + y * I, by simpa using hy⟩) n := by
  -- pointwise: `q(u + iy)^{-n} = e^{2π n y} e^{-2π i n u}`
  have hq : ∀ u : ℝ, (1 / Function.Periodic.qParam 1 ((u : ℂ) + y * ↑UpperHalfPlane.I) ^ n : ℂ) =
      ↑(Real.exp (2 * π * n * y)) * fourier (-(n : ℤ)) (u : AddCircle ((1 : ℝ) - 0)) := by
    intro u
    rw [fourier_coe_apply, Function.Periodic.qParam, UpperHalfPlane.coe_I, one_div,
      ← Complex.exp_nat_mul, ← Complex.exp_neg, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    linear_combination (-(2 * π * n * y)) * Complex.I_sq
  -- keep `1 - 0` in the `AddCircle` index: only the scalar factor is normalised
  have hone : (1 : ℝ) / (1 - 0) = 1 := by norm_num
  rw [qExpansion_coeff_eq_intervalIntegral one_pos hfper hfhol hfbdd n hy,
    fourierCoeffOn_eq_integral, Complex.ofReal_one, div_one, one_mul, hone, one_smul,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun u _ ↦ ?_
  simp only [smul_eq_mul]
  rw [hq u, mul_assoc]
  rfl

/-- The restriction of a continuous function on `ℍ` to the horizontal line `Im τ = y`. -/
theorem continuous_horizontal_slice {f : ℍ → ℂ} (hf : Continuous f) {y : ℝ} (hy : 0 < y) :
    Continuous fun x : ℝ ↦ f ⟨x + y * I, by simpa using hy⟩ := by
  refine hf.comp (UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr ?_)
  exact (by fun_prop : Continuous fun x : ℝ ↦ (x : ℂ) + y * I)

/-- **Bessel's inequality on a horizontal line.** The truncated sum
`∑_{n < M} ‖a n‖ ^ 2 * exp (-4 π n y)` is bounded by `∫₀¹ ‖f (x + i y)‖ ^ 2 dx`. -/
theorem sum_range_norm_sq_qExpansion_coeff_mul_exp_le {f : ℍ → ℂ}
    (hfper : Function.Periodic (f ∘ ofComplex) 1) (hfhol : MDiff f)
    (hfbdd : IsBoundedAtImInfty f) {y : ℝ} (hy : 0 < y) (M : ℕ) :
    ∑ n ∈ range M, ‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * y)) ≤
      ∫ x in (0 : ℝ)..1, ‖f ⟨x + y * I, by simpa using hy⟩‖ ^ 2 := by
  set g : ℝ → ℂ := fun x ↦ f ⟨x + y * I, by simpa using hy⟩ with hg_def
  have hg : Continuous g := continuous_horizontal_slice hfhol.continuous hy
  -- Parseval for the slice, indexed by `ℤ`
  have hP := hasSum_sq_fourierCoeffOn zero_lt_one (memLp_two_restrict_Ioc_of_continuous hg 0 1)
  simp only [sub_zero, inv_one, one_smul] at hP
  -- termwise: `‖a n‖ ^ 2 * exp (-4 π n y) = ‖c n‖ ^ 2`
  have hterm : ∀ n : ℕ, ‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * y)) =
      ‖fourierCoeffOn zero_lt_one g n‖ ^ 2 := by
    intro n
    have h1 : Real.exp (2 * π * n * y) ^ 2 * Real.exp (-(4 * π * n * y)) = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_zero]
      congr 1
      push_cast
      ring
    rw [qExpansion_coeff_eq_exp_mul_fourierCoeffOn hfper hfhol hfbdd hy n, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow]
    linear_combination ‖fourierCoeffOn zero_lt_one g n‖ ^ 2 * h1
  rw [Finset.sum_congr rfl fun n _ ↦ hterm n,
    ← Finset.sum_image (f := fun i : ℤ ↦ ‖fourierCoeffOn zero_lt_one g i‖ ^ 2)
      (Nat.cast_injective.injOn (s := (range M : Set ℕ)))]
  exact sum_le_hasSum _ (fun i _ ↦ by positivity) hP

/-! ### The mean-square bound for cusp forms -/

variable {N k : ℕ}

/-- `1` is a strict period of `Γ₁(N)`, since `T ∈ Γ₁(N)`. -/
theorem one_mem_strictPeriods_gammaOne (N : ℕ) :
    (1 : ℝ) ∈ (GammaOne N).strictPeriods := by
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 N := by
    rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.coe_T]
  unfold GammaOne
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples 1

/-- Hecke's bound (Rudnick, Lemma 1.1(b)): `‖f τ‖ ^ 2 * (im τ) ^ k` is bounded on `ℍ`. -/
theorem exists_norm_sq_mul_im_pow_le [NeZero N] (f : CuspForm (GammaOne N) (k : ℤ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℍ, ‖f τ‖ ^ 2 * τ.im ^ k ≤ C := by
  have : (GammaOne N).IsArithmetic := by unfold GammaOne; infer_instance
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound f
  refine ⟨C ^ 2, sq_nonneg C, fun τ ↦ ?_⟩
  have hτ := τ.im_pos
  have h1 : ‖f τ‖ ^ 2 ≤ (C / τ.im ^ (((k : ℤ) : ℝ) / 2)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hC τ) 2
  have h2 : (τ.im ^ (((k : ℤ) : ℝ) / 2)) ^ 2 = τ.im ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hτ.le, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  rw [div_pow, h2] at h1
  exact (le_div_iff₀ (by positivity)).1 h1

/-- **Mean-square bound** (Rudnick, proof of Theorem 1.2, inequality (1)):
`∑_{n < M} ‖a n‖ ^ 2 ≤ D * M ^ k`. -/
theorem exists_sum_range_norm_sq_qExpansion_coeff_le [NeZero N]
    (f : CuspForm (GammaOne N) (k : ℤ)) :
    ∃ D : ℝ, ∀ M : ℕ, ∑ n ∈ range M, ‖(qExpansion 1 f).coeff n‖ ^ 2 ≤ D * (M : ℝ) ^ k := by
  have : (GammaOne N).IsArithmetic := by unfold GammaOne; infer_instance
  obtain ⟨C, hC0, hC⟩ := exists_norm_sq_mul_im_pow_le f
  have hfper : Function.Periodic (f ∘ ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods_gammaOne N)
  have hfhol : MDiff f := ModularFormClass.holo f
  have hfbdd : IsBoundedAtImInfty f := ModularFormClass.bdd_at_infty f
  refine ⟨Real.exp (4 * π) * C, fun M ↦ ?_⟩
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp only [Finset.range_zero, Finset.sum_empty]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le hC0) (pow_nonneg (Nat.cast_nonneg _) _)
  have hy : (0 : ℝ) < 1 / M := by positivity
  -- Hecke's bound on the line `Im τ = 1 / M` reads `‖f τ‖ ^ 2 ≤ C * M ^ k`
  have key : ∀ τ : ℍ, τ.im = 1 / M → ‖f τ‖ ^ 2 ≤ C * (M : ℝ) ^ k := by
    intro τ hτ
    have h := hC τ
    rwa [hτ, one_div_pow, mul_one_div, div_le_iff₀ (by positivity)] at h
  -- the integral of `‖f‖ ^ 2` over the segment at height `1 / M` is at most `C * M ^ k`
  have hint : ∫ x in (0 : ℝ)..1, ‖f ⟨x + (1 / M : ℝ) * I, by simpa using hy⟩‖ ^ 2 ≤
      C * (M : ℝ) ^ k := by
    calc ∫ x in (0 : ℝ)..1, ‖f ⟨x + (1 / M : ℝ) * I, by simpa using hy⟩‖ ^ 2
        ≤ ∫ _x in (0 : ℝ)..1, C * (M : ℝ) ^ k := by
          refine intervalIntegral.integral_mono_on zero_le_one
            (((continuous_horizontal_slice hfhol.continuous hy).norm.pow 2).intervalIntegrable 0 1)
            intervalIntegrable_const fun x _ ↦ key _ ?_
          show ((x : ℂ) + ((1 / M : ℝ) : ℂ) * I).im = 1 / M
          simp
      _ = C * (M : ℝ) ^ k := by simp
  -- `exp (-4 π n / M) ≥ exp (-4 π)` for `n < M`
  have hterm : ∀ n ∈ range M, ‖(qExpansion 1 f).coeff n‖ ^ 2 ≤
      Real.exp (4 * π) * (‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * (1 / M)))) := by
    intro n hn
    rw [Finset.mem_range] at hn
    have hnM : (n : ℝ) * (1 / M) ≤ 1 := by
      rw [mul_one_div, div_le_one (by positivity)]
      exact_mod_cast hn.le
    have h1 : Real.exp (-(4 * π)) ≤ Real.exp (-(4 * π * n * (1 / M))) := by
      apply Real.exp_le_exp.2
      nlinarith [Real.pi_pos, hnM]
    calc ‖(qExpansion 1 f).coeff n‖ ^ 2
        = ‖(qExpansion 1 f).coeff n‖ ^ 2 * (Real.exp (4 * π) * Real.exp (-(4 * π))) := by
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      _ ≤ ‖(qExpansion 1 f).coeff n‖ ^ 2 * (Real.exp (4 * π) * Real.exp (-(4 * π * n * (1 / M)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le)
            (by positivity)
      _ = Real.exp (4 * π) * (‖(qExpansion 1 f).coeff n‖ ^ 2 *
            Real.exp (-(4 * π * n * (1 / M)))) := by ring
  calc ∑ n ∈ range M, ‖(qExpansion 1 f).coeff n‖ ^ 2
      ≤ ∑ n ∈ range M, Real.exp (4 * π) *
          (‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * (1 / M)))) :=
        Finset.sum_le_sum hterm
    _ = Real.exp (4 * π) * ∑ n ∈ range M,
          ‖(qExpansion 1 f).coeff n‖ ^ 2 * Real.exp (-(4 * π * n * (1 / M))) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (4 * π) * ∫ x in (0 : ℝ)..1, ‖f ⟨x + (1 / M : ℝ) * I, by simpa using hy⟩‖ ^ 2 :=
        mul_le_mul_of_nonneg_left
          (sum_range_norm_sq_qExpansion_coeff_mul_exp_le hfper hfhol hfbdd hy M) (Real.exp_pos _).le
    _ ≤ Real.exp (4 * π) * (C * (M : ℝ) ^ k) := mul_le_mul_of_nonneg_left hint (Real.exp_pos _).le
    _ = Real.exp (4 * π) * C * (M : ℝ) ^ k := by ring

end MTT

set_option linter.unusedVariables false in
theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (f : CuspForm (MTT.GammaOne N) (k : ℤ)) :
    Summable (fun m : ℕ =>
      ‖(UpperHalfPlane.qExpansion 1 f).coeff m‖^2 * Real.log m /
        (m : ℝ)^(k+1)) := by
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨D, hD⟩ := MTT.exists_sum_range_norm_sq_qExpansion_coeff_le f
  exact MTT.summable_mul_log_div_pow_of_sum_range_le (fun n ↦ by positivity) hD
