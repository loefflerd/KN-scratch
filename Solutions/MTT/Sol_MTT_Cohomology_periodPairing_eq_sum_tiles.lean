import Definitions.MTT.Def_MTT_PeriodPairing
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.GroupTheory.Complement
import Mathlib.Tactic.FieldSimp
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

noncomputable section

section PeriodMeasureComparison

set_option autoImplicit false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Modular ComplexConjugate

namespace MTT.Cohomology

theorem tsum_quotient_inv_eq_sum_complement {G : Type*} [Group G]
    (H : Subgroup G) (R : Finset G)
    (hR : Subgroup.IsComplement (H : Set G) (R : Set G)) (I : G → ℂ)
    (hI : ∀ γ ∈ H, ∀ g, I (γ * g) = I g) :
    (∑' q : G ⧸ H, I q.out⁻¹) = ∑ g ∈ R, I g := by
  classical
  let e : (G ⧸ H) ≃ (R : Set G) :=
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm.trans
      hR.rightQuotientEquiv
  have he (q : G ⧸ H) : e q = hR.toRightFun q.out⁻¹ :=
    congrArg (fun q => hR.rightQuotientEquiv
      ((QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm q))
      q.out_eq.symm
  calc
    _ = ∑' q : G ⧸ H, I (e q) := by
      apply tsum_congr
      intro q
      rw [he]
      simpa only [inv_mul_cancel_right] using
        hI _ (hR.mul_inv_toRightFun_mem q.out⁻¹) (hR.toRightFun q.out⁻¹)
    _ = ∑' g : (R : Set G), I g := e.tsum_eq (fun g : (R : Set G) => I g)
    _ = _ := by
      rw [tsum_fintype]
      exact Finset.sum_coe_sort R I

theorem setIntegral_im_sq_mul (F : ℂ → ℂ) {s : Set ℍ} (hs : MeasurableSet s) :
    (∫ z in s, (z.im : ℂ) ^ 2 * F z) =
      ∫ z in UpperHalfPlane.coe '' s, F z := by
  have hm : MeasurePreserving UpperHalfPlane.coe (volume.comap UpperHalfPlane.coe)
      (volume.restrict (Set.range UpperHalfPlane.coe)) :=
    ⟨measurable_coe, by rw [measurableEmbedding_coe.map_comap]⟩
  rw [UpperHalfPlane.volume_def,
    setIntegral_withDensity_eq_setIntegral_smul (by fun_prop) _ hs]
  calc
    _ = ∫ z in s, F z ∂(volume.comap UpperHalfPlane.coe) := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [NNReal.smul_def, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one,
        NNReal.coe_mk, Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_div,
        Complex.ofReal_one]
      have hz : (z.im : ℂ) ≠ 0 := by exact_mod_cast z.im_ne_zero
      field_simp
    _ = _ := by
      rw [← hm.setIntegral_image_emb measurableEmbedding_coe]
      rw [Measure.restrict_restrict (measurableEmbedding_coe.measurableSet_image.mpr hs),
        Set.inter_eq_self_of_subset_left (Set.image_subset_range _ _)]

theorem setIntegral_image_smul_im_sq_mul (F : ℂ → ℂ) (g : SL(2, ℤ))
    {s : Set ℍ} (hs : MeasurableSet s) :
    (∫ z : ℍ in s, ((g • z).im : ℂ) ^ 2 * F (g • z : ℍ)) =
      ∫ z in (fun τ : ℍ => ((g • τ : ℍ) : ℂ)) '' s, F z := by
  have hm : MeasurePreserving (fun z : ℍ => g • z) volume volume :=
    measurePreserving_smul (Matrix.SpecialLinearGroup.mapGL ℝ g) volume
  have he : MeasurableEmbedding (fun z : ℍ => g • z) :=
    measurableEmbedding_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ g)
  rw [← hm.setIntegral_image_emb he (fun z : ℍ => (z.im : ℂ) ^ 2 * F z) s]
  rw [setIntegral_im_sq_mul F (he.measurableSet_image.mpr hs), Set.image_image]

theorem periodDomainIntegral_eq_sum_complement (N : ℕ) (F : ℍ → ℂ)
    (hF : ∀ γ ∈ CongruenceSubgroup.Gamma1 N, ∀ z : ℍ, F (γ • z) = F z)
    (R : Finset SL(2, ℤ))
    (hR : Subgroup.IsComplement (CongruenceSubgroup.Gamma1 N : Set SL(2, ℤ))
      (R : Set SL(2, ℤ))) :
    periodDomainIntegral N F = ∑ σ ∈ R, ∫ z in ModularGroup.fd, F (σ • z) := by
  unfold periodDomainIntegral
  refine tsum_quotient_inv_eq_sum_complement _ R hR
    (fun σ => ∫ z in ModularGroup.fd, F (σ • z)) ?_
  intro γ hγ σ
  apply integral_congr_ae
  filter_upwards [] with z
  rw [mul_smul, hF γ hγ]

theorem periodDomainIntegral_density_eq_sum_tiles (N : ℕ) (F : ℂ → ℂ)
    (hF : ∀ γ ∈ CongruenceSubgroup.Gamma1 N, ∀ z : ℍ,
      ((γ • z).im : ℂ) ^ 2 * F (γ • z : ℍ) = (z.im : ℂ) ^ 2 * F z)
    (R : Finset SL(2, ℤ))
    (hR : Subgroup.IsComplement (CongruenceSubgroup.Gamma1 N : Set SL(2, ℤ))
      (R : Set SL(2, ℤ))) :
    periodDomainIntegral N (fun z => (z.im : ℂ) ^ 2 * F z) =
      ∑ σ ∈ R, ∫ z in (fun τ : ℍ => ((σ • τ : ℍ) : ℂ)) '' ModularGroup.fd,
        F z := by
  rw [periodDomainIntegral_eq_sum_complement N _ hF R hR]
  apply Finset.sum_congr rfl
  intro σ hσ
  exact setIntegral_image_smul_im_sq_mul F σ ModularGroup.isClosed_fd.measurableSet

end MTT.Cohomology

end PeriodMeasureComparison

section PeriodContractionComputations
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

end PeriodContractionComputations

section PeriodPairingTiles

set_option autoImplicit false
open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Modular ComplexConjugate

namespace MTT.Cohomology

private theorem period_density_invariant {N k : ℕ} (hk : 2 ≤ k)
    (f q : CuspForm (MTT.GammaOne N) (k : ℤ))
    {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma1 N) (z : ℍ) :
    ((γ • z).im : ℂ) ^ 2 * periodContraction (k - 2)
        (f (γ • z) • periodPower (k - 2) (γ • z : ℍ))
        (conj (q (γ • z)) • periodPower (k - 2) (conj (γ • z : ℍ))) =
      (z.im : ℂ) ^ 2 * periodContraction (k - 2)
        (f z • periodPower (k - 2) z)
        (conj (q z) • periodPower (k - 2) (conj (z : ℂ))) := by
  rw [MTT.PeriodMeasure.periodDensity_eq_petersson hk,
    MTT.PeriodMeasure.periodDensity_eq_petersson hk]
  congr 1
  exact SlashInvariantFormClass.petersson_smul (f := q) (f' := f)
    (show Matrix.SpecialLinearGroup.mapGL ℝ γ ∈ MTT.GammaOne N from
      ⟨γ, hγ, rfl⟩)

theorem periodPairing_eq_sum_tiles_aux {N k : ℕ} (hk : 2 ≤ k)
    (f q : CuspForm (MTT.GammaOne N) (k : ℤ))
    (R : Finset SL(2, ℤ))
    (hR : Subgroup.IsComplement (CongruenceSubgroup.Gamma1 N : Set SL(2, ℤ))
      (R : Set SL(2, ℤ)))
    (D : ℂ → ℂ)
    (hD : ∀ z : ℍ, D z = periodContraction (k - 2)
      (f z • periodPower (k - 2) z)
      (conj (q z) • periodPower (k - 2) (conj (z : ℂ)))) :
    periodPairing N (k - 2) f q =
      ∑ σ ∈ R, ∫ z in (fun τ : ℍ => ((σ • τ : ℍ) : ℂ)) '' ModularGroup.fd,
        D z := by
  have hF (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma1 N) (z : ℍ) :
      ((γ • z).im : ℂ) ^ 2 * D (γ • z : ℍ) = (z.im : ℂ) ^ 2 * D z := by
    rw [hD, hD]
    exact period_density_invariant hk f q hγ z
  simpa only [periodPairing, hD] using
    periodDomainIntegral_density_eq_sum_tiles N D hF R hR

end MTT.Cohomology

end PeriodPairingTiles

open UpperHalfPlane MeasureTheory MTT.Cohomology
open scoped MatrixGroups Modular ComplexConjugate

theorem solution {N k : ℕ} (hk : 2 ≤ k)
    (f q : CuspForm (MTT.GammaOne N) (k : ℤ))
    (R : Finset SL(2, ℤ))
    (hR : Subgroup.IsComplement (CongruenceSubgroup.Gamma1 N : Set SL(2, ℤ))
      (R : Set SL(2, ℤ)))
    (D : ℂ → ℂ)
    (hD : ∀ z : ℍ, D z = periodContraction (k - 2)
      (f z • periodPower (k - 2) z)
      (conj (q z) • periodPower (k - 2) (conj (z : ℂ)))) :
    periodPairing N (k - 2) f q =
      ∑ σ ∈ R, ∫ z in (fun τ : ℍ => ((σ • τ : ℍ) : ℂ)) '' ModularGroup.fd,
        D z :=
  MTT.Cohomology.periodPairing_eq_sum_tiles_aux hk f q R hR D hD
