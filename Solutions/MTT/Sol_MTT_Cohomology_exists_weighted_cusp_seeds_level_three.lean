import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.RingTheory.PowerSeries.Expand

import Definitions.MTT.Def_MTT_Arithmetic
import Theorems.FLT.Thm_CongruenceSubgroup_closure_T_U_neg_one_eq_Gamma0_three
import Theorems.FLT.Thm_CuspForm_exists_gamma0_apply_eq_eta_mul_pow_twentyfour
import Theorems.FLT.Thm_EisensteinSeries_exists_modularForm_coe_eq_eisensteinG
import Theorems.FLT.Thm_EisensteinSeries_qExpansion_eisensteinG_coeff
import Theorems.FLT.Thm_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul

noncomputable section

/-! # Elementary eta identities used by the level-three construction

The translation and inversion identities are adapted from Claude's accepted
Prove2Me proof 9f9d7099-dd4e-5af0-8131-7c3e5d2d1482, originally from
anthropics/fermats-last-theorem commit aa2d8b34692b16c70f699536de0d8e75b9a3e9ef.
Only the required identities are included; no resource overrides or macros
are copied. The level-three modularity and cusp argument below is new.
-/

section EtaIdentities
open scoped MatrixGroups ModularForm Real UpperHalfPlane
open ModularGroup Complex
open ModularForm (eta eta_q eta_q_eq_cexp)
namespace MTT.Cohomology.EtaFour

lemma eta_q_add_int (n : ℕ) (w : ℂ) (m : ℤ) : eta_q n (w + m) = eta_q n w := by
  rw [eta_q_eq_cexp, eta_q_eq_cexp]
  have : 2 * ↑π * I * (↑n + 1) * (w + ↑m) =
      2 * ↑π * I * (↑n + 1) * w + ((((n : ℤ) + 1) * m : ℤ) : ℂ) * (2 * π * I) := by
    push_cast
    ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma eta_add_int (w : ℂ) (m : ℤ) : η (w + m) = cexp (π * I * m / 12) * η w := by
  unfold ModularForm.eta
  simp_rw [eta_q_add_int]
  rw [Function.Periodic.qParam, Function.Periodic.qParam, ← mul_assoc]
  congr 1
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma eta_add_int_pow (w : ℂ) (m : ℤ) (e : ℕ) :
    η (w + m) ^ e = cexp (π * I * (m * e) / 12) * η w ^ e := by
  rw [eta_add_int, mul_pow, ← Complex.exp_nat_mul]
  congr 2
  ring

lemma sqrt_sq (w : ℂ) : Complex.sqrt w ^ 2 = w := by
  have h := Complex.cpow_nat_inv_pow w two_ne_zero
  have h2 : ((2 : ℕ) : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by norm_num
  rw [h2] at h
  exact h

lemma eta_neg_inv (w : ℂ) (hw : 0 < w.im) :
    η (-w⁻¹) = (Complex.sqrt I)⁻¹ * (Complex.sqrt w * η w) := by
  have := ModularForm.eta_comp_eq_csqrt_I_inv hw
  rw [show -w⁻¹ = -1 / w by rw [neg_div, one_div]]
  simpa only [Function.comp, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] using this

lemma eta_neg_inv_pow (w : ℂ) (hw : 0 < w.im) (e : ℕ) :
    η (-w⁻¹) ^ (2 * e) = (I⁻¹ * w) ^ e * η w ^ (2 * e) := by
  rw [eta_neg_inv w hw]
  have : ((Complex.sqrt I)⁻¹ * (Complex.sqrt w * η w)) ^ (2 * e) =
      ((Complex.sqrt I ^ 2)⁻¹ * (Complex.sqrt w ^ 2)) ^ e * (η w ^ 2) ^ e := by ring
  rw [this, sqrt_sq, sqrt_sq, ← pow_mul]

lemma coe_S_smul (z : ℍ) : ((ModularGroup.S • z : ℍ) : ℂ) = -((z : ℂ))⁻¹ := by
  rw [UpperHalfPlane.modular_S_smul]; simp [inv_neg]

lemma denom_SL (γ : SL(2, ℤ)) (z : ℍ) :
    UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) (z : ℂ) =
      (γ 1 0 : ℂ) * z + (γ 1 1 : ℂ) := by
  simp [UpperHalfPlane.denom]

lemma denom_S (z : ℍ) :
    UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) ModularGroup.S)) (z : ℂ) = z := by
  rw [denom_SL]; simp [ModularGroup.coe_S]

lemma denom_T_zpow (n : ℤ) (z : ℍ) :
    UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))
        (ModularGroup.T ^ n))) (z : ℂ) = 1 := by
  rw [denom_SL]; simp [ModularGroup.coe_T_zpow]

lemma coe_T_zpow_smul (n : ℤ) (z : ℍ) :
    ((ModularGroup.T ^ n • z : ℍ) : ℂ) = (z : ℂ) + n := by
  rw [UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd]; push_cast; ring

lemma coe_T_smul (z : ℍ) : ((ModularGroup.T • z : ℍ) : ℂ) = (z : ℂ) + 1 := by
  rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd]; push_cast; ring

lemma denom_T (z : ℍ) :
    UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) ModularGroup.T)) (z : ℂ) = 1 := by
  rw [denom_SL]; simp [ModularGroup.coe_T]

end MTT.Cohomology.EtaFour
end EtaIdentities

section WeightOneThreeSeed

open UpperHalfPlane

theorem MTT.Cohomology.exists_weight_one_seed_level_three :
    ∃ A : ModularForm (MTT.GammaOne 3) 1, (qExpansion 1 A).order = 0 := by
  obtain ⟨A, _, hA, _⟩ := ModularForm.exists_weight_one_gamma1_three_slash_fricke_eq_smul
  refine ⟨A, PowerSeries.order_eq_nat.mpr ⟨?_, ?_⟩⟩
  · simpa only [hA] using (one_ne_zero : (1 : ℂ) ≠ 0)
  · intro i hi
    exact (Nat.not_lt_zero i hi).elim

end WeightOneThreeSeed

section WeightThreeEisenstein

/-! # A weight-three Eisenstein series vanishing at infinity on Gamma1(3) -/

open UpperHalfPlane Matrix
open scoped MatrixGroups ModularForm

namespace MTT.Cohomology

def threeRow (b : ZMod 3) : Fin 2 → ZMod 3 := ![1, b]

def threeEis (b : ZMod 3) : ModularForm (CongruenceSubgroup.Gamma 3) 3 :=
  (EisensteinSeries.exists_modularForm_coe_eq_eisensteinG 3 3 (by norm_num)
    (threeRow b)).1.choose

theorem threeEis_coe (b : ZMod 3) :
    (threeEis b : UpperHalfPlane → ℂ) = EisensteinSeries.eisensteinG 3 3 (threeRow b) :=
  (EisensteinSeries.exists_modularForm_coe_eq_eisensteinG 3 3 (by norm_num)
    (threeRow b)).1.choose_spec

theorem threeRow_mul (b : ZMod 3) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma1 3) :
    threeRow b ᵥ* γ = threeRow (b + (γ 0 1 : ZMod 3)) := by
  obtain ⟨ha, hd, hc⟩ := (CongruenceSubgroup.Gamma1_mem 3 γ).mp hγ
  ext i
  fin_cases i <;>
    simp [threeRow, Matrix.vecMul, dotProduct, Fin.sum_univ_two, ha, hd, hc, add_comm]

def threeEisSum : ModularForm (CongruenceSubgroup.Gamma 3) 3 := ∑ b : ZMod 3, threeEis b

theorem threeEisSum_coe : (threeEisSum : UpperHalfPlane → ℂ) =
    ∑ b : ZMod 3, EisensteinSeries.eisensteinG 3 3 (threeRow b) := by
  change FunLike.coeAddMonoidHom _ _ _ (∑ b : ZMod 3, threeEis b) = _
  rw [map_sum]
  simp only [FunLike.coeAddMonoidHom_apply, threeEis_coe]

theorem threeEisSum_slash (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma1 3) :
    (threeEisSum : UpperHalfPlane → ℂ) ∣[(3 : ℤ)] γ = threeEisSum := by
  rw [threeEisSum_coe, SlashAction.sum_slash]
  simp_rw [(EisensteinSeries.exists_modularForm_coe_eq_eisensteinG
    3 3 (by norm_num) _).2, threeRow_mul _ γ hγ]
  exact Equiv.sum_comp (Equiv.addRight (γ 0 1 : ZMod 3))
    (fun b => EisensteinSeries.eisensteinG 3 3 (threeRow b))

def threeEisGammaOne : ModularForm (MTT.GammaOne 3) 3 :=
  { toFun := threeEisSum
    slash_action_eq' := by
      rintro _ ⟨γ, hγ, rfl⟩
      exact threeEisSum_slash γ hγ
    holo' := threeEisSum.holo'
    bdd_at_cusps' := fun hc => threeEisSum.bdd_at_cusps'
      ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z
        (CongruenceSubgroup.Gamma 3 : Subgroup (GL (Fin 2) ℝ))).mpr
        ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z (MTT.GammaOne 3)).mp hc)) }

end MTT.Cohomology

end WeightThreeEisenstein

section QExpansionWidthThree

/-! # Comparing q-expansions of widths one and three -/

open UpperHalfPlane
open scoped MatrixGroups

namespace MTT.Cohomology

theorem qParam_three_pow (z : ℂ) :
    Function.Periodic.qParam 3 z ^ 3 = Function.Periodic.qParam 1 z := by
  unfold Function.Periodic.qParam
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem qExpansion_three_coeff_mul {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (F : ModularForm Γ k) (h₁ : (1 : ℝ) ∈ Γ.strictPeriods)
    (h₃ : (3 : ℝ) ∈ Γ.strictPeriods) (n : ℕ) :
    (qExpansion 3 F).coeff (3 * n) = (qExpansion 1 F).coeff n := by
  let : Fact (IsCusp OnePoint.infty Γ) :=
    ⟨Γ.isCusp_of_mem_strictPeriods (by norm_num) h₁⟩
  let Q := PowerSeries.expand 3 (by decide) (qExpansion 1 F)
  have he (j : ℕ) : Q.coeff j = (qExpansion 3 F).coeff j := by
    refine ModularFormClass.qExpansion_coeff_unique (f := F)
      (c := fun m => Q.coeff m) (by norm_num) h₃ ?_ j
    intro z
    have hinj : Function.Injective (fun m : ℕ => 3 * m) := by
      intro a b hab
      dsimp only at hab
      omega
    apply (hinj.hasSum_iff (f := fun m => Q.coeff m •
      Function.Periodic.qParam 3 z ^ m) ?_).mp
    · have h := ModularForm.hasSum_qExpansion F (by norm_num) h₁ z
      apply h.congr_fun
      intro m
      change Q.coeff (3 * m) * Function.Periodic.qParam 3 z ^ (3 * m) =
        (qExpansion 1 F).coeff m * Function.Periodic.qParam 1 z ^ m
      rw [PowerSeries.coeff_expand_mul, pow_mul, qParam_three_pow]
    · intro m hm
      have hd : ¬ 3 ∣ m := by
        rintro ⟨j, hj⟩
        exact hm ⟨j, hj.symm⟩
      change Q.coeff m * Function.Periodic.qParam 3 z ^ m = 0
      rw [PowerSeries.coeff_expand_of_not_dvd 3 (by decide) _ hd, zero_mul]
  rw [← he (3 * n), PowerSeries.coeff_expand_mul]

end MTT.Cohomology

end QExpansionWidthThree

section WeightThreeCoefficients

/-! # The first coefficients of the level-three Eisenstein sum -/

open UpperHalfPlane
open scoped MatrixGroups

namespace MTT.Cohomology

theorem threeEisSum_coeff (n : ℕ) :
    (qExpansion 3 threeEisSum).coeff n =
      ∑ b : ZMod 3, (qExpansion 3 (threeEis b)).coeff n := by
  have hΓ : (3 : ℝ) ∈
      (CongruenceSubgroup.Gamma 3 : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma]
    exact AddSubgroup.mem_zmultiples 3
  have hq : qExpansion 3 threeEisSum = ∑ b : ZMod 3, qExpansion 3 (threeEis b) :=
    map_sum (ModularForm.qExpansionAddHom (by norm_num) hΓ 3) threeEis Finset.univ
  rw [hq, map_sum]

theorem threeEis_coeff_zero (b : ZMod 3) : (qExpansion 3 (threeEis b)).coeff 0 = 0 := by
  have h := EisensteinSeries.qExpansion_eisensteinG_coeff 3 3 (by decide) (threeRow b) 0
  norm_num [threeRow] at h
  simpa only [threeEis_coe, threeRow, PowerSeries.coeff_zero_eq_constantCoeff] using h

theorem threeEis_coeff_three (b : ZMod 3) :
    (qExpansion 3 (threeEis b)).coeff 3 =
      (-2 * Real.pi * Complex.I) ^ 3 / (2 * 27) * 9 := by
  have h := EisensteinSeries.qExpansion_eisensteinG_coeff 3 3 (by decide) (threeRow b) 3
  norm_num [threeRow, show Nat.divisors 3 = {1, 3} from by decide,
    show (3 : ZMod 3) = 0 from by decide,
    show (1 : ZMod 3) ≠ -1 from by decide] at h
  rw [show (3 : ZMod 3) = 0 from by decide] at h
  norm_num at h
  convert h using 1 <;> norm_num [threeEis_coe, threeRow]

theorem threeEisGammaOne_coeff_zero : (qExpansion 1 threeEisGammaOne).coeff 0 = 0 := by
  have h₁ : (1 : ℝ) ∈ (MTT.GammaOne 3).strictPeriods := by
    change (1 : ℝ) ∈ (CongruenceSubgroup.Gamma1 3 : Subgroup (GL (Fin 2) ℝ)).strictPeriods
    rw [CongruenceSubgroup.strictPeriods_Gamma1]
    exact AddSubgroup.mem_zmultiples 1
  have h₃ : (3 : ℝ) ∈ (MTT.GammaOne 3).strictPeriods := by
    convert (MTT.GammaOne 3).strictPeriods.nsmul_mem h₁ 3 using 1; norm_num
  rw [← qExpansion_three_coeff_mul threeEisGammaOne h₁ h₃ 0]
  change (qExpansion 3 threeEisSum).coeff 0 = 0
  simp only [threeEisSum_coeff, threeEis_coeff_zero, Finset.sum_const_zero]

theorem threeEisGammaOne_coeff_one : (qExpansion 1 threeEisGammaOne).coeff 1 ≠ 0 := by
  have h₁ : (1 : ℝ) ∈ (MTT.GammaOne 3).strictPeriods := by
    change (1 : ℝ) ∈ (CongruenceSubgroup.Gamma1 3 : Subgroup (GL (Fin 2) ℝ)).strictPeriods
    rw [CongruenceSubgroup.strictPeriods_Gamma1]
    exact AddSubgroup.mem_zmultiples 1
  have h₃ : (3 : ℝ) ∈ (MTT.GammaOne 3).strictPeriods := by
    convert (MTT.GammaOne 3).strictPeriods.nsmul_mem h₁ 3 using 1; norm_num
  rw [← qExpansion_three_coeff_mul threeEisGammaOne h₁ h₃ 1]
  change (qExpansion 3 threeEisSum).coeff 3 ≠ 0
  rw [threeEisSum_coeff]
  simp only [threeEis_coeff_three, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul]
  exact mul_ne_zero (by norm_num)
    (mul_ne_zero (div_ne_zero (pow_ne_zero _
      (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        Complex.I_ne_zero)) (by norm_num)) (by norm_num))

theorem exists_weight_three_seed_level_three :
    ∃ B : ModularForm (MTT.GammaOne 3) 3, PowerSeries.order (qExpansion 1 B) = 1 := by
  refine ⟨threeEisGammaOne, PowerSeries.order_eq_nat.mpr ⟨threeEisGammaOne_coeff_one, ?_⟩⟩
  intro n hn
  have : n = 0 := by omega
  subst n
  exact threeEisGammaOne_coeff_zero

end MTT.Cohomology

end WeightThreeCoefficients

section EtaThreeTransformations

/-! # Transformations of the weight-six level-three eta product

The eta translation and inversion identities are the attributed elementary
identities already used for the level-four seed; the level-three argument is new.
-/


open UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace MTT.Cohomology.EtaThree

open EtaFour (eta_add_int_pow eta_neg_inv_pow denom_T denom_S coe_T_smul coe_S_smul
  denom_T_zpow coe_T_zpow_smul)

def Dc (z : ℂ) : ℂ := ModularForm.eta z ^ 6 * ModularForm.eta (3 * z) ^ 6

def D (z : UpperHalfPlane) : ℂ := Dc z

def Gc (z : ℂ) : ℂ := ModularForm.eta z ^ 6 * ModularForm.eta (z / 3) ^ 6

def factor : ℂ := (Complex.I⁻¹) ^ 6 * (3⁻¹ : ℂ) ^ 3

theorem Dc_add_one (z : ℂ) : Dc (z + 1) = Dc z := by
  unfold Dc
  rw [show 3 * (z + 1) = 3 * z + ((3 : ℤ) : ℂ) by push_cast; ring]
  rw [show z + 1 = z + ((1 : ℤ) : ℂ) by norm_num,
    eta_add_int_pow, eta_add_int_pow]
  have h : Complex.exp (Real.pi * Complex.I * ((1 : ℤ) * 6) / 12) *
      Complex.exp (Real.pi * Complex.I * ((3 : ℤ) * 6) / 12) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_two_pi_mul_I using 1; congr 1; push_cast; ring
  calc
    _ = (Complex.exp (Real.pi * Complex.I * ((1 : ℤ) * 6) / 12) *
        Complex.exp (Real.pi * Complex.I * ((3 : ℤ) * 6) / 12)) *
        (ModularForm.eta z ^ 6 * ModularForm.eta (3 * z) ^ 6) := by push_cast; ring
    _ = _ := by rw [h, one_mul]

theorem Gc_add_three (z : ℂ) : Gc (z + ((3 : ℤ) : ℂ)) = Gc z := by
  unfold Gc
  rw [show (z + ((3 : ℤ) : ℂ)) / 3 = z / 3 + ((1 : ℤ) : ℂ) by push_cast; ring,
    eta_add_int_pow, eta_add_int_pow]
  have h : Complex.exp (Real.pi * Complex.I * ((3 : ℤ) * 6) / 12) *
      Complex.exp (Real.pi * Complex.I * ((1 : ℤ) * 6) / 12) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_two_pi_mul_I using 1; congr 1; push_cast; ring
  calc
    _ = (Complex.exp (Real.pi * Complex.I * ((3 : ℤ) * 6) / 12) *
        Complex.exp (Real.pi * Complex.I * ((1 : ℤ) * 6) / 12)) *
        (ModularForm.eta z ^ 6 * ModularForm.eta (z / 3) ^ 6) := by push_cast; ring
    _ = _ := by rw [h, one_mul]

theorem Dc_neg_inv (z : ℂ) (hz : 0 < z.im) :
    Dc (-z⁻¹) = factor * z ^ 6 * Gc z := by
  have hz3 : 0 < (z / 3).im := by rw [Complex.div_ofNat_im]; positivity
  unfold Dc Gc factor
  rw [show 3 * -z⁻¹ = -(z / 3)⁻¹ by rw [inv_div]; ring]
  change ModularForm.eta (-z⁻¹) ^ (2 * 3) * ModularForm.eta (-(z / 3)⁻¹) ^ (2 * 3) = _
  rw [eta_neg_inv_pow z hz, eta_neg_inv_pow (z / 3) hz3]
  ring

theorem D_slash_T : D ∣[(6 : ℤ)] ModularGroup.T = D := by
  funext z
  rw [ModularForm.SL_slash_apply, denom_T, one_zpow, mul_one]
  change Dc (ModularGroup.T • z : UpperHalfPlane) = Dc z
  rw [coe_T_smul, Dc_add_one]

theorem D_slash_S :
    D ∣[(6 : ℤ)] ModularGroup.S = fun z : UpperHalfPlane => factor * Gc z := by
  funext z
  rw [ModularForm.SL_slash_apply, denom_S]
  change Dc (ModularGroup.S • z : UpperHalfPlane) * (z : ℂ) ^ (-6 : ℤ) = _
  rw [coe_S_smul, Dc_neg_inv _ z.im_pos]
  simp only [zpow_neg, zpow_ofNat]
  field_simp [z.ne_zero]

def lower : SL(2, ℤ) := ⟨!![1, 0; -3, 1], by decide⟩

theorem D_slash_lower : D ∣[(6 : ℤ)] lower = D := by
  have ht : (D ∣[(6 : ℤ)] ModularGroup.S) ∣[(6 : ℤ)]
      (ModularGroup.T ^ (3 : ℤ)) = D ∣[(6 : ℤ)] ModularGroup.S := by
    rw [D_slash_S]
    funext z
    rw [ModularForm.SL_slash_apply, denom_T_zpow, one_zpow, mul_one]
    simp only [coe_T_zpow_smul, Gc_add_three]
  have hu : lower =
      ModularGroup.S * ModularGroup.T ^ (3 : ℤ) * ModularGroup.S⁻¹ := by decide
  rw [hu, SlashAction.slash_mul, SlashAction.slash_mul, ht,
    ← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]

end MTT.Cohomology.EtaThree

end EtaThreeTransformations

section CuspSquareRoot

open UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace UpperHalfPlane

theorem isZeroAtImInfty_of_square {f : UpperHalfPlane → ℂ}
    (h : IsZeroAtImInfty (f * f)) : IsZeroAtImInfty f := by
  rw [isZeroAtImInfty_iff] at h ⊢
  intro ε hε
  obtain ⟨A, hA⟩ := h (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨A, fun z hz => ?_⟩
  have hi := hA z hz
  simp only [Pi.mul_apply, norm_mul] at hi
  nlinarith [norm_nonneg (f z)]

end UpperHalfPlane

namespace OnePoint

theorem IsZeroAt.of_mul_self {c : OnePoint ℝ} {f : UpperHalfPlane → ℂ} {k : ℤ}
    (hc : IsCusp c 𝒮ℒ) (hf : c.IsZeroAt (f * f) (k + k)) : c.IsZeroAt f k := by
  apply (isZeroAt_iff_forall_SL2Z hc).mpr
  intro γ hγ
  have h := (isZeroAt_iff_forall_SL2Z hc).mp hf γ hγ
  rw [ModularForm.mul_slash_SL2] at h
  exact UpperHalfPlane.isZeroAtImInfty_of_square h

end OnePoint

end CuspSquareRoot

section WeightSixThreeSeed

/-! # A nonzero weight-six cusp form on Gamma1(3) -/

open UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace MTT.Cohomology.EtaThree

theorem D_slash_gammaZero :
    ∀ γ ∈ (CongruenceSubgroup.Gamma0 3 : Subgroup (GL (Fin 2) ℝ)),
      D ∣[(6 : ℤ)] γ = D := by
  have hΓ : (CongruenceSubgroup.Gamma0 3 : Subgroup (GL (Fin 2) ℝ)) =
      Subgroup.closure ((Matrix.SpecialLinearGroup.mapGL ℝ) ''
        ({ModularGroup.T, lower, -1} : Set SL(2, ℤ))) := by
    rw [← CongruenceSubgroup.closure_T_U_neg_one_eq_Gamma0_three lower rfl,
      MonoidHom.map_closure]
  rw [SlashInvariantForm.slash_action_generators hΓ]
  rintro _ ⟨γ, hγ, rfl⟩
  rcases hγ with rfl | rfl | rfl
  · exact D_slash_T
  · exact D_slash_lower
  · funext z
    change (D ∣[(6 : ℤ)] (-1 : SL(2, ℤ))) z = D z
    rw [ModularForm.SL_slash_apply, EtaFour.denom_SL]
    norm_num

theorem D_mdifferentiable :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) D := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hDc : DifferentiableOn ℂ Dc {z : ℂ | 0 < z.im} := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    have hz' : 0 < z.im := hz
    have h3 : 0 < (3 * z).im := by simp [Complex.mul_im]; positivity
    exact ((ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hz').pow _).mul
      (((ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet h3).comp z
        (differentiableAt_id.const_mul _)).pow _)
  refine hDc.congr fun z hz => ?_
  have hz' : 0 < z.im := hz
  simp [D, Function.comp, UpperHalfPlane.ofComplex_apply_of_im_pos hz']

theorem exists_fourth_power_cusp :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 3) 24,
      (g : UpperHalfPlane → ℂ) = (D * D) * (D * D) := by
  obtain ⟨g₁, hg₁⟩ := CuspForm.exists_gamma0_apply_eq_eta_mul_pow_twentyfour 1
  obtain ⟨g₃, hg₃⟩ := CuspForm.exists_gamma0_apply_eq_eta_mul_pow_twentyfour 3
  have hlevel : (CongruenceSubgroup.Gamma0 3 : Subgroup (GL (Fin 2) ℝ)) ≤
      (CongruenceSubgroup.Gamma0 1 : Subgroup (GL (Fin 2) ℝ)) := by
    apply Subgroup.map_mono
    intro γ _
    exact CongruenceSubgroup.Gamma0_mem.mpr (Subsingleton.elim _ _)
  let g₁' : CuspForm (CongruenceSubgroup.Gamma0 3) 12 :=
    { toFun := g₁
      slash_action_eq' := fun γ hγ => g₁.slash_action_eq' γ (hlevel hγ)
      holo' := g₁.holo'
      zero_at_cusps' := fun hc => g₁.zero_at_cusps' (hc.mono hlevel) }
  refine ⟨g₁'.mulModularForm (g₃ : ModularForm (CongruenceSubgroup.Gamma0 3) 12), ?_⟩
  funext z
  change g₁ z * g₃ z = (D z * D z) * (D z * D z)
  rw [hg₁, hg₃]
  simp only [Nat.cast_one, Nat.cast_ofNat, one_mul, D, Dc]
  ring

theorem D_zero_at {c : OnePoint ℝ} (hc : IsCusp c (MTT.GammaOne 3)) :
    c.IsZeroAt D 6 := by
  obtain ⟨g, hg⟩ := exists_fourth_power_cusp
  have hcSL := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z (MTT.GammaOne 3)).mp hc
  apply OnePoint.IsZeroAt.of_mul_self (k := 6) hcSL
  rw [show (6 : ℤ) + 6 = 12 by norm_num]
  apply OnePoint.IsZeroAt.of_mul_self (k := 12) hcSL
  rw [show (12 : ℤ) + 12 = 24 by norm_num, ← hg]
  exact g.zero_at_cusps' (hc.mono
    (Subgroup.map_mono (CongruenceSubgroup.Gamma1_in_Gamma0 3)))

end MTT.Cohomology.EtaThree

namespace MTT.Cohomology

theorem exists_weight_six_cusp_seed_level_three :
    ∃ D : CuspForm (MTT.GammaOne 3) 6, D ≠ 0 := by
  let D : CuspForm (MTT.GammaOne 3) 6 :=
    { toFun := EtaThree.D
      slash_action_eq' := fun γ hγ => EtaThree.D_slash_gammaZero γ
        ((Subgroup.map_mono (CongruenceSubgroup.Gamma1_in_Gamma0 3)) hγ)
      holo' := EtaThree.D_mdifferentiable
      zero_at_cusps' := EtaThree.D_zero_at }
  refine ⟨D, ?_⟩
  intro hd
  have hz := congrArg (fun f : CuspForm (MTT.GammaOne 3) 6 => f I) hd
  have hne : EtaThree.D I ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (ModularForm.eta_ne_zero I.im_pos))
      (pow_ne_zero _ (ModularForm.eta_ne_zero (by norm_num [Complex.mul_im])))
  exact hne hz

end MTT.Cohomology

end WeightSixThreeSeed

section LevelThreeSeeds

/-! # All three analytic seeds for the level-three cusp-dimension bound -/

open UpperHalfPlane

theorem MTT.Cohomology.exists_weighted_cusp_seeds_level_three_aux :
    ∃ A : ModularForm (MTT.GammaOne 3) 1,
      ∃ B : ModularForm (MTT.GammaOne 3) 3,
        ∃ D : CuspForm (MTT.GammaOne 3) 6,
          MvPowerSeries.order (qExpansion 1 A) = 0 ∧
            MvPowerSeries.order (qExpansion 1 B) = 1 ∧ D ≠ 0 := by
  obtain ⟨A, hA⟩ := MTT.Cohomology.exists_weight_one_seed_level_three
  obtain ⟨B, hB⟩ := MTT.Cohomology.exists_weight_three_seed_level_three
  obtain ⟨D, hD⟩ := MTT.Cohomology.exists_weight_six_cusp_seed_level_three
  exact ⟨A, B, D, PowerSeries.order_eq_order.symm.trans hA,
    PowerSeries.order_eq_order.symm.trans hB, hD⟩

end LevelThreeSeeds

theorem solution :
    ∃ A : ModularForm (MTT.GammaOne 3) 1,
      ∃ B : ModularForm (MTT.GammaOne 3) 3,
        ∃ D : CuspForm (MTT.GammaOne 3) 6,
          MvPowerSeries.order (UpperHalfPlane.qExpansion 1 A) = 0 ∧
            MvPowerSeries.order (UpperHalfPlane.qExpansion 1 B) = 1 ∧ D ≠ 0 :=
  MTT.Cohomology.exists_weighted_cusp_seeds_level_three_aux
