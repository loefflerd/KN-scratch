/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.MTT.Def_MTT_PeriodPairing
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Integrability of the period density on modular tiles -/

noncomputable section

section Part0
/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.AINTLIB.
Authors: Chris Birkbeck

Adapted from AINTLIB, PeterssonInnerProduct.lean, commit
eb9621e7bcb0ce220ad53983ec45d987cb5b9002. Uses mathlib's canonical measure.
-/

set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure UpperHalfPlane Complex Set
open scoped MatrixGroups Modular ComplexConjugate NNReal

namespace MTT.Analytic

private lemma strip_lintegral_lt_top {c : ℝ} (hc : 0 < c) :
    ∫⁻ p in Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ Ioi c,
      ENNReal.ofReal (p.2 ^ (-2 : ℤ)) ∂(volume : Measure (ℝ × ℝ)) < ⊤ := by
  have hi : IntegrableOn (fun y : ℝ => y ^ (-2 : ℤ)) (Ioi c) := by
    simpa only [← Real.rpow_intCast, Int.cast_neg, Int.cast_ofNat] using
      integrableOn_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) hc
  rw [volume_eq_prod ℝ ℝ, setLIntegral_prod_symm _ (by fun_prop)]
  simp_rw [setLIntegral_const, Real.volume_Icc]
  norm_num
  exact lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi
    fun y _ => Real.ofReal_le_enorm _) hi.hasFiniteIntegral

/-- The standard modular fundamental domain has finite hyperbolic area. -/
theorem volume_fd_lt_top : volume (ModularGroup.fd : Set ℍ) < ⊤ := by
  let T := Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ Ioi (1 / 2 : ℝ)
  let F : ℂ → ENNReal := fun z => ENNReal.ofReal (z.im ^ (-2 : ℤ))
  have hprod : ∫⁻ z in equivRealProd ⁻¹' T, F z =
      ∫⁻ p in T, ENNReal.ofReal (p.2 ^ (-2 : ℤ)) := by
    rw [show (⇑equivRealProd : ℂ → ℝ × ℝ) = ⇑measurableEquivRealProd from rfl]
    have h := volume_preserving_equiv_real_prod.setLIntegral_comp_emb
        measurableEquivRealProd.measurableEmbedding
        (fun p : ℝ × ℝ => ENNReal.ofReal (p.2 ^ (-2 : ℤ)))
        (measurableEquivRealProd ⁻¹' T)
    rw [MeasurableEquiv.image_preimage] at h
    simpa only [measurableEquivRealProd_apply, F] using h
  rw [UpperHalfPlane.volume_eq_lintegral]
  calc
    _ = ∫⁻ z in UpperHalfPlane.coe '' ModularGroup.fd, F z := by
      apply setLIntegral_congr_fun
        (measurableEmbedding_coe.measurableSet_image.mpr
          ModularGroup.isClosed_fd.measurableSet)
      rintro _ ⟨z, _, rfl⟩
      change (↑((1 / ‖z.im‖₊) ^ 2 : ℝ≥0) : ENNReal) =
        ENNReal.ofReal (z.im ^ (-2 : ℤ))
      rw [← ENNReal.ofReal_coe_nnreal]
      congr 1
      simp [Real.nnnorm_of_nonneg z.im_pos.le, zpow_neg]
    _ ≤ ∫⁻ z in equivRealProd ⁻¹' T, F z := by
      apply lintegral_mono_set
      rintro _ ⟨z, hz, rfl⟩
      refine ⟨?_, ?_⟩
      · simpa only [equivRealProd_apply, coe_re, mem_Icc, neg_div] using abs_le.mp hz.2
      have := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
      change 1 / 2 < z.im
      nlinarith [z.im_pos]
    _ = _ := hprod
    _ < ⊤ := strip_lintegral_lt_top (by norm_num)

theorem integrableOn_petersson_smul_fd {k : ℤ}
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f q : CuspForm Γ k) (σ : SL(2, ℤ)) :
    IntegrableOn (fun z : ℍ => petersson k q f (σ • z)) ModularGroup.fd := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k Γ q f
  refine IntegrableOn.of_bound volume_fd_lt_top ?_ C (.of_forall fun z => hC _)
  exact ((petersson_continuous k (ModularFormClass.continuous q)
    (ModularFormClass.continuous f)).comp
      (continuous_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ σ))).aestronglyMeasurable
        |>.restrict

end MTT.Analytic

end Part0

section Part1
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The coefficient and contraction proofs are adapted from cbirkbeck's accepted
Prove2Me proof 777707bf-f8aa-4fd9-8d82-71afe645b027, Part A.
-/

set_option autoImplicit false
open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Modular ComplexConjugate

namespace MTT.PeriodMeasure
open MTT.Cohomology

private lemma binaryExponent_apply (n j : ℕ) (i : Fin 2) :
    binaryExponent n j i = if i = 0 then j else n - j := by
  simp [binaryExponent]

private lemma single_add_single_eq (n j : ℕ) :
    Finsupp.single (0 : Fin 2) j + Finsupp.single 1 (n - j) = binaryExponent n j := by
  ext i
  fin_cases i <;> simp [binaryExponent_apply]

lemma coeff_periodPower (n j : ℕ) (hj : j ≤ n) (z : ℂ) :
    AddMonoidAlgebra.coeff (periodPower n z) (binaryExponent n j) =
      (n.choose j : ℂ) * z ^ j := by
  unfold periodPower
  rw [add_pow, MvPolynomial.coeff_sum]
  have key : ∀ m ∈ Finset.range (n + 1),
      AddMonoidAlgebra.coeff ((MvPolynomial.C z * MvPolynomial.X 0) ^ m * MvPolynomial.X 1 ^ (n - m) *
          (n.choose m : MvPolynomial (Fin 2) ℂ)) (binaryExponent n j)
        = if m = j then (n.choose j : ℂ) * z ^ j else 0 := by
    intro m _
    have hmono : (MvPolynomial.C z * MvPolynomial.X 0) ^ m * MvPolynomial.X 1 ^ (n - m) *
          (n.choose m : MvPolynomial (Fin 2) ℂ)
        = MvPolynomial.monomial (Finsupp.single (0 : Fin 2) m + Finsupp.single 1 (n - m))
            ((n.choose m : ℂ) * z ^ m) := by
      rw [mul_pow, ← MvPolynomial.C_pow, MvPolynomial.X_pow_eq_monomial,
        MvPolynomial.X_pow_eq_monomial, ← map_natCast MvPolynomial.C (n.choose m),
        MvPolynomial.C_mul_monomial, MvPolynomial.monomial_mul_monomial,
        mul_comm (MvPolynomial.monomial _ _) (MvPolynomial.C _),
        MvPolynomial.C_mul_monomial]
      congr 1
      ring
    rw [hmono, MvPolynomial.coeff_monomial]
    by_cases hmj : m = j
    · subst hmj
      rw [ite_eq_left (single_add_single_eq n m), ite_eq_left rfl]
    · have hne : Finsupp.single (0 : Fin 2) m + Finsupp.single 1 (n - m) ≠
          binaryExponent n j := by
        intro h
        apply hmj
        have := DFunLike.congr_fun h 0
        simpa [binaryExponent_apply] using this
      rw [ite_eq_right hne, ite_eq_right hmj]
  rw [Finset.sum_congr rfl key]
  simp [Finset.sum_ite_eq', Nat.lt_succ_of_le hj]

lemma periodContraction_smul_smul (n : ℕ) (a b : ℂ) (P Q : Binary ℂ) :
    periodContraction n (a • P) (b • Q) = a * b * periodContraction n P Q := by
  unfold periodContraction
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

lemma periodContraction_periodPower (n : ℕ) (z w : ℂ) :
    periodContraction n (periodPower n z) (periodPower n w) = (z - w) ^ n := by
  unfold periodContraction
  rw [sub_eq_add_neg, add_pow]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hj' : j ≤ n := by omega
  rw [coeff_periodPower n j hj' z,
    coeff_periodPower n (n - j) (Nat.sub_le n j) w, Nat.choose_symm hj']
  have hc : (n.choose j : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj').ne'
  rw [neg_pow]
  field_simp
  ring

lemma periodDensity_eq_petersson {k : ℕ} (hk : 2 ≤ k) (f q : ℍ → ℂ) (z : ℍ) :
    (z.im : ℂ) ^ 2 * periodContraction (k - 2) (f z • periodPower (k - 2) z)
        (conj (q z) • periodPower (k - 2) (conj (z : ℂ))) =
      (2 * Complex.I) ^ (k - 2) * petersson (k : ℤ) q f z := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [periodContraction_smul_smul, periodContraction_periodPower, Complex.sub_conj,
    UpperHalfPlane.coe_im, petersson, zpow_natCast]
  push_cast
  ring

end MTT.PeriodMeasure

end Part1

section Part2

set_option autoImplicit false
open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Modular ComplexConjugate NNReal

namespace MTT.Cohomology

theorem integrableOn_im_sq_mul_iff (F : ℂ → ℂ) {s : Set ℍ}
    (hs : MeasurableSet s) :
    IntegrableOn (fun z : ℍ => (z.im : ℂ) ^ 2 * F z) s ↔
      IntegrableOn F (UpperHalfPlane.coe '' s) := by
  have hm : MeasurePreserving UpperHalfPlane.coe (volume.comap UpperHalfPlane.coe)
      (volume.restrict (Set.range UpperHalfPlane.coe)) :=
    ⟨measurable_coe, by rw [measurableEmbedding_coe.map_comap]⟩
  change Integrable _ (volume.restrict s) ↔ _
  rw [UpperHalfPlane.volume_def, restrict_withDensity hs,
    integrable_withDensity_iff_integrable_smul (by fun_prop)]
  have heq : (fun z : ℍ => ((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2) •
      ((z.im : ℂ) ^ 2 * F z)) = fun z : ℍ => F z := by
    funext z
    simp only [NNReal.smul_def, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one,
      NNReal.coe_mk, Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_div,
      Complex.ofReal_one]
    have hz : (z.im : ℂ) ≠ 0 := by exact_mod_cast z.im_ne_zero
    field_simp
  rw [heq]
  change IntegrableOn _ s _ ↔ _
  have hi := hm.integrableOn_image measurableEmbedding_coe (f := F) (s := s)
  rw [IntegrableOn, Measure.restrict_restrict
      (measurableEmbedding_coe.measurableSet_image.mpr hs),
    Set.inter_eq_self_of_subset_left (Set.image_subset_range _ _)] at hi
  exact hi.symm

theorem integrableOn_image_smul_im_sq_mul_iff (F : ℂ → ℂ) (σ : SL(2, ℤ))
    {s : Set ℍ} (hs : MeasurableSet s) :
    IntegrableOn (fun z : ℍ => ((σ • z).im : ℂ) ^ 2 * F (σ • z : ℍ)) s ↔
      IntegrableOn F ((fun z : ℍ => ((σ • z : ℍ) : ℂ)) '' s) := by
  have hm : MeasurePreserving (fun z : ℍ => σ • z) volume volume :=
    measurePreserving_smul (Matrix.SpecialLinearGroup.mapGL ℝ σ) volume
  have he : MeasurableEmbedding (fun z : ℍ => σ • z) :=
    measurableEmbedding_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ σ)
  simpa only [Function.comp_def, Set.image_image] using
    (hm.integrableOn_image he (f := fun z : ℍ => (z.im : ℂ) ^ 2 * F z)
      (s := s)).symm.trans
        (integrableOn_im_sq_mul_iff F (he.measurableSet_image.mpr hs))

theorem periodDensity_integrableOn_tile_aux {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (f q : CuspForm (MTT.GammaOne N) (k : ℤ)) (σ : SL(2, ℤ))
    (D : ℂ → ℂ)
    (hD : ∀ z : ℍ, D z = periodContraction (k - 2)
      (f z • periodPower (k - 2) z)
      (conj (q z) • periodPower (k - 2) (conj (z : ℂ)))) :
    IntegrableOn D ((fun z : ℍ => ((σ • z : ℍ) : ℂ)) '' ModularGroup.fd) := by
  let : NeZero N := ⟨hN.ne'⟩
  rw [← integrableOn_image_smul_im_sq_mul_iff D σ ModularGroup.isClosed_fd.measurableSet]
  simpa only [hD, MTT.PeriodMeasure.periodDensity_eq_petersson hk, IntegrableOn] using
    (MTT.Analytic.integrableOn_petersson_smul_fd f q σ).const_mul
      ((2 * Complex.I) ^ (k - 2))

end MTT.Cohomology

end Part2

open UpperHalfPlane MeasureTheory MTT.Cohomology
open scoped MatrixGroups Modular ComplexConjugate

theorem solution {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (f q : CuspForm (MTT.GammaOne N) (k : ℤ)) (σ : SL(2, ℤ))
    (D : ℂ → ℂ)
    (hD : ∀ z : ℍ, D z = periodContraction (k - 2)
      (f z • periodPower (k - 2) z)
      (conj (q z) • periodPower (k - 2) (conj (z : ℂ)))) :
    IntegrableOn D ((fun z : ℍ => ((σ • z : ℍ) : ℂ)) '' ModularGroup.fd) :=
  MTT.Cohomology.periodDensity_integrableOn_tile_aux hN hk f q σ D hD
