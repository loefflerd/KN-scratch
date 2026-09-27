import Definitions.MTT.Def_MTT_Arithmetic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Field.GeomSum
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Complex UpperHalfPlane

namespace MTT

theorem qParam_mul_nat (h : ℝ) (p : ℕ) (z : ℂ) :
    Function.Periodic.qParam h (↑p * z) = Function.Periodic.qParam h z ^ p := by
  simp only [Function.Periodic.qParam, ← exp_nat_mul]; congr 1; ring

theorem qParam_add (h : ℝ) (z w : ℂ) :
    Function.Periodic.qParam h (z + w) =
      Function.Periodic.qParam h z * Function.Periodic.qParam h w := by
  simp only [Function.Periodic.qParam, add_div, mul_add, exp_add]

theorem im_pos_shift_div (τ : ℍ) (b : ℕ) {p : ℕ} (hp : 0 < p) :
    0 < (((τ : ℂ) + (b : ℂ)) / (p : ℂ)).im := by
  rw [Complex.div_natCast_im, Complex.add_im, Complex.natCast_im, add_zero]
  exact div_pos τ.im_pos (Nat.cast_pos.mpr hp)

theorem im_pos_nat_mul (τ : ℍ) {p : ℕ} (hp : 0 < p) : 0 < ((p : ℂ) * (τ : ℂ)).im := by
  simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
  exact mul_pos (Nat.cast_pos.mpr hp) τ.im_pos

/-- Root-of-unity orthogonality at period one. -/
theorem sum_qParam_pow_period_one {p : ℕ} (hp : Nat.Prime p) (n : ℕ) :
    ∑ b ∈ Finset.range p, Function.Periodic.qParam (1 : ℝ) (1 / (↑p : ℂ)) ^ (n * b) =
      if p ∣ n then (↑p : ℂ) else 0 := by
  set ζ := Function.Periodic.qParam (1 : ℝ) (1 / (↑p : ℂ)) with hζ_def
  have hζ_prim : IsPrimitiveRoot ζ p := by
    rw [hζ_def, Function.Periodic.qParam]
    convert Complex.isPrimitiveRoot_exp p hp.ne_zero using 1; push_cast; ring_nf
  split_ifs with hpn
  · simp_rw [pow_mul ζ n, (hζ_prim.pow_eq_one_iff_dvd n).mpr hpn, one_pow,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  · have hζn_ne : ζ ^ n ≠ 1 := mt (hζ_prim.pow_eq_one_iff_dvd n).mp hpn
    simp_rw [pow_mul ζ n]
    rw [geom_sum_eq hζn_ne, show (ζ ^ n) ^ p = 1 from by
      rw [← pow_mul, mul_comm, pow_mul, hζ_prim.pow_eq_one, one_pow]]
    simp

/-- **The upper-triangular part.** If `f = Σ a n q^n` at every point of `ℍ`, then
`p⁻¹ Σ_{b<p} f((τ+b)/p) = Σ a (p n) q^n`. -/
theorem hasSum_heckePrime_upper {p : ℕ} (hp : Nat.Prime p) (f : ℍ → ℂ) (a : ℕ → ℂ) (τ : ℍ)
    (hf : ∀ σ : ℍ, HasSum (fun n ↦ a n • Function.Periodic.qParam (1 : ℝ) ↑σ ^ n) (f σ)) :
    HasSum (fun n ↦ a (p * n) • Function.Periodic.qParam (1 : ℝ) ↑τ ^ n)
      ((p : ℂ)⁻¹ * ∑ b : Fin p, f (ofComplex (((τ : ℂ) + (b.val : ℂ)) / (p : ℂ)))) := by
  set q := Function.Periodic.qParam (1 : ℝ) ↑τ with hq_def
  have hp_ne : (↑p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hinj : Function.Injective (p * · : ℕ → ℕ) := mul_right_injective₀ hp.ne_zero
  set w := Function.Periodic.qParam (1 : ℝ) ((↑τ : ℂ) / ↑p) with hw_def
  set ζ := Function.Periodic.qParam (1 : ℝ) (1 / (↑p : ℂ)) with hζ_def
  have hw_pow_p : w ^ p = q := by
    rw [hw_def, ← qParam_mul_nat]; congr 1; field_simp
  let σ : ℕ → ℍ := fun b ↦ ⟨((τ : ℂ) + (b : ℂ)) / (p : ℂ), im_pos_shift_div τ b hp.pos⟩
  have hσ : ∀ b : ℕ, ofComplex (((τ : ℂ) + (b : ℂ)) / (p : ℂ)) = σ b := fun b ↦
    ofComplex_apply_of_im_pos _
  have hqσ : ∀ (b n : ℕ),
      Function.Periodic.qParam (1 : ℝ) ↑(σ b) ^ n = w ^ n * ζ ^ (n * b) := by
    intro b n
    show Function.Periodic.qParam (1 : ℝ) (((τ : ℂ) + (b : ℂ)) / (p : ℂ)) ^ n = _
    rw [add_div, qParam_add, show (↑b : ℂ) / ↑p = ↑b * (1 / ↑p) from by ring, qParam_mul_nat,
      mul_pow, ← pow_mul, mul_comm b n]
  have h_rewritten : HasSum (fun n ↦ a n * (w ^ n * ∑ b ∈ Finset.range p, ζ ^ (n * b)))
      (∑ b ∈ Finset.range p, f (σ b)) := by
    convert hasSum_sum (fun b (_ : b ∈ Finset.range p) ↦ hf (σ b)) using 2 with n
    simp_rw [smul_eq_mul, hqσ]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
  have h_ind : HasSum (fun n' ↦ (if p ∣ n' then a n' * w ^ n' else 0))
      ((↑p : ℂ)⁻¹ * ∑ b ∈ Finset.range p, f (σ b)) := by
    have h_scaled := h_rewritten.const_smul (↑p : ℂ)⁻¹
    simp only [smul_eq_mul] at h_scaled
    convert h_scaled using 1
    funext n
    rw [sum_qParam_pow_period_one hp n]
    split_ifs with h
    · field_simp
    · simp
  have h_re : HasSum (fun m ↦ a (p * m) * q ^ m)
      ((↑p : ℂ)⁻¹ * ∑ b ∈ Finset.range p, f (σ b)) := by
    have := (hinj.hasSum_iff (f := fun n' ↦ (if p ∣ n' then a n' * w ^ n' else 0)) (fun x hx ↦ by
      simp only [Set.mem_range, not_exists] at hx
      simp [show ¬ p ∣ x from fun ⟨c, hc⟩ ↦ hx c (by omega)])).mpr h_ind
    convert this using 1
    funext m
    simp only [Function.comp_def, dvd_mul_right, if_true, pow_mul, hw_pow_p]
  have hS : (∑ b : Fin p, f (ofComplex (((τ : ℂ) + (b.val : ℂ)) / (p : ℂ)))) =
      ∑ b ∈ Finset.range p, f (σ b) := by
    rw [Fin.sum_univ_eq_sum_range (fun b : ℕ ↦ f (ofComplex (((τ : ℂ) + (b : ℂ)) / (p : ℂ)))) p]
    exact Finset.sum_congr rfl fun b _ ↦ congrArg f (hσ b)
  simpa [smul_eq_mul, hS] using h_re

/-- **The lower part.** If `f = Σ a n q^n`, then `f(pτ) = Σ_{p ∣ m} a (m/p) q^m`. -/
theorem hasSum_heckePrime_lower {p : ℕ} (hp : Nat.Prime p) (f : ℍ → ℂ) (a : ℕ → ℂ) (τ : ℍ)
    (hf : ∀ σ : ℍ, HasSum (fun n ↦ a n • Function.Periodic.qParam (1 : ℝ) ↑σ ^ n) (f σ)) :
    HasSum (fun m ↦ (if p ∣ m then a (m / p) else 0) • Function.Periodic.qParam (1 : ℝ) ↑τ ^ m)
      (f (ofComplex ((p : ℂ) * (τ : ℂ)))) := by
  set q := Function.Periodic.qParam (1 : ℝ) ↑τ with hq_def
  have hinj : Function.Injective (p * · : ℕ → ℕ) := mul_right_injective₀ hp.ne_zero
  let pτ : ℍ := ⟨(p : ℂ) * (τ : ℂ), im_pos_nat_mul τ hp.pos⟩
  have hpτ : ofComplex ((p : ℂ) * (τ : ℂ)) = pτ := ofComplex_apply_of_im_pos _
  rw [hpτ]
  refine (hinj.hasSum_iff (fun x hx ↦ ?_)).mp ?_
  · simp only [Set.mem_range, not_exists] at hx
    simp [show ¬ p ∣ x from fun ⟨c, hc⟩ ↦ hx c (by omega)]
  · have := hf pτ
    convert this using 1
    funext n
    simp only [Function.comp_def, dvd_mul_right, if_true, Nat.mul_div_cancel_left _ hp.pos]
    show a n • q ^ (p * n) = a n • Function.Periodic.qParam (1 : ℝ) ((p : ℂ) * (τ : ℂ)) ^ n
    rw [qParam_mul_nat, ← pow_mul]

end MTT

theorem solution (k : ℕ) (e : ℂ) {p : ℕ} (hp : Nat.Prime p)
    (f : UpperHalfPlane → ℂ) (a : ℕ → ℂ) (τ : UpperHalfPlane)
    (hf : ∀ σ : UpperHalfPlane,
      HasSum (fun n ↦ a n • Function.Periodic.qParam (1 : ℝ) (σ : ℂ) ^ n) (f σ)) :
    HasSum (fun n ↦ (a (p * n) + e * (p : ℂ) ^ (k - 1) * (if p ∣ n then a (n / p) else 0)) •
        Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ n)
      (MTT.heckePrime k e p f τ) := by
  have hu := MTT.hasSum_heckePrime_upper hp f a τ hf
  have hl := (MTT.hasSum_heckePrime_lower hp f a τ hf).const_smul (e * (p : ℂ) ^ (k - 1))
  convert hu.add hl using 1
  · funext n
    simp only [smul_eq_mul]
    split_ifs <;> ring
  · simp only [MTT.heckePrime, smul_eq_mul]
