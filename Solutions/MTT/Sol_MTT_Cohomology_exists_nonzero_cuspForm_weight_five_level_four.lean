import Mathlib.Data.Int.Star
import Mathlib.GroupTheory.Schreier
import Mathlib.NumberTheory.ModularForms.Discriminant

import Definitions.MTT.Def_MTT_Arithmetic
import Theorems.FLT.Thm_CuspForm_exists_gamma0_four_apply_eq_eta_pow_mul


/-! # A six-coset Schreier computation for Gamma0(4)

The transversal argument follows the platform's level-three generator proof
by adapting its row-label calculation to the nonfield ZMod 4.
-/

section

open Matrix CongruenceSubgroup Subgroup
open scoped MatrixGroups Pointwise

namespace MTT.Cohomology.GammaZeroFour

def lower : SL(2, ℤ) := ⟨!![1, 0; -4, 1], by simp [Matrix.det_fin_two]⟩

def rep : Fin 6 → SL(2, ℤ)
  | 0 => 1
  | 1 => ModularGroup.S
  | 2 => ⟨!![0, -1; 1, 1], by decide⟩
  | 3 => ⟨!![0, -1; 1, 2], by decide⟩
  | 4 => ⟨!![0, -1; 1, 3], by decide⟩
  | 5 => ⟨!![1, 0; 2, 1], by decide⟩

def rowLabel (c d : ZMod 4) : Fin 6 :=
  if c = 0 then 0 else if c = 2 then 5 else
    ⟨1 + (c * d).val, by have := (c * d).val_lt; omega⟩

def label (g : SL(2, ℤ)) : Fin 6 := rowLabel (g 1 0) (g 1 1)

theorem rowLabel_spec (c d : ZMod 4) (h : ∃ a b : ZMod 4, a * d - b * c = 1)
    (l : Fin 6) :
    c * (rep l 1 1 : ZMod 4) = d * (rep l 1 0 : ZMod 4) ↔ l = rowLabel c d := by
  have hf : ∀ c d : ZMod 4, (∃ a b : ZMod 4, a * d - b * c = 1) →
      ∀ l : Fin 6,
        c * (rep l 1 1 : ZMod 4) = d * (rep l 1 0 : ZMod 4) ↔ l = rowLabel c d := by
    decide +kernel
  exact hf c d h l

theorem mul_inv_mem_iff (g h : SL(2, ℤ)) :
    g * h⁻¹ ∈ Gamma0 4 ↔
      (g 1 0 : ZMod 4) * (h 1 1 : ZMod 4) = (g 1 1 : ZMod 4) * (h 1 0 : ZMod 4) := by
  rw [Gamma0_mem]
  have he : (g * h⁻¹) 1 0 = g 1 0 * h 1 1 - g 1 1 * h 1 0 := by
    simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg]
  rw [he]
  push_cast
  exact sub_eq_zero

theorem mul_inv_rep_mem_iff (g : SL(2, ℤ)) (l : Fin 6) :
    g * (rep l)⁻¹ ∈ Gamma0 4 ↔ l = label g := by
  rw [mul_inv_mem_iff]
  apply rowLabel_spec
  refine ⟨g 0 0, g 0 1, ?_⟩
  have hd := g.property
  rw [Matrix.det_fin_two] at hd
  have he := congrArg (Int.castRingHom (ZMod 4)) hd
  simpa only [map_sub, map_mul, map_one, Int.coe_castRingHom] using he

def transversal : Set SL(2, ℤ) := Set.range rep

theorem isComplement_transversal :
    IsComplement (Gamma0 4 : Set SL(2, ℤ)) transversal := by
  rw [isComplement_iff_existsUnique_mul_inv_mem]
  intro g
  refine ⟨⟨rep (label g), ⟨label g, rfl⟩⟩, (mul_inv_rep_mem_iff g _).mpr rfl, ?_⟩
  rintro ⟨x, l, rfl⟩ hx
  exact Subtype.ext (congrArg rep ((mul_inv_rep_mem_iff g l).mp hx))

theorem coe_toRightFun (g : SL(2, ℤ)) :
    (isComplement_transversal.toRightFun g : SL(2, ℤ)) = rep (label g) := by
  have hu := isComplement_iff_existsUnique_mul_inv_mem.mp isComplement_transversal g
  have h₁ := isComplement_transversal.mul_inv_toRightFun_mem g
  have h₂ : g * ((⟨rep (label g), ⟨label g, rfl⟩⟩ : transversal) : SL(2, ℤ))⁻¹ ∈
      (Gamma0 4 : Set SL(2, ℤ)) := (mul_inv_rep_mem_iff g _).mpr rfl
  exact congrArg Subtype.val (hu.unique h₁ h₂)

def schreierGen (l : Fin 6) (s : SL(2, ℤ)) : SL(2, ℤ) :=
  rep l * s * (rep (label (rep l * s)))⁻¹

def schreierGens : Set SL(2, ℤ) :=
  {x | ∃ l : Fin 6, x = schreierGen l ModularGroup.S ∨ x = schreierGen l ModularGroup.T}

theorem closure_schreierGens : Subgroup.closure schreierGens = Gamma0 4 := by
  refine le_antisymm ((Subgroup.closure_le _).mpr ?_) ?_
  · rintro x ⟨l, rfl | rfl⟩ <;> exact (mul_inv_rep_mem_iff _ _).mpr rfl
  · rw [← Subgroup.closure_mul_image_eq isComplement_transversal
      (show (1 : SL(2, ℤ)) ∈ transversal from ⟨0, rfl⟩)
      SpecialLinearGroup.SL2Z_generators]
    refine Subgroup.closure_mono ?_
    rintro x ⟨g, hg, rfl⟩
    obtain ⟨r, hr, s, hs, rfl⟩ := Set.mem_mul.mp hg
    obtain ⟨l, rfl⟩ := hr
    simp only [coe_toRightFun]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact ⟨l, Or.inl rfl⟩
    · exact ⟨l, Or.inr rfl⟩

theorem schreier_table_S :
    (fun l => schreierGen l ModularGroup.S) =
      ![1, -1, ModularGroup.T⁻¹ * lower⁻¹, lower * -1,
        (lower * ModularGroup.T) * -1, lower⁻¹] := by
  funext l
  fin_cases l <;> decide +kernel

theorem schreier_table_T :
    (fun l => schreierGen l ModularGroup.T) =
      ![ModularGroup.T, 1, 1, 1, lower, (lower⁻¹ * ModularGroup.T⁻¹) * -1] := by
  funext l
  fin_cases l <;> decide +kernel

theorem closure_T_lower_neg_one :
    Subgroup.closure ({ModularGroup.T, lower, -1} : Set SL(2, ℤ)) = Gamma0 4 := by
  let H := Subgroup.closure ({ModularGroup.T, lower, -1} : Set SL(2, ℤ))
  have hT : ModularGroup.T ∈ H := Subgroup.subset_closure (Or.inl rfl)
  have hU : lower ∈ H := Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have hz : (-1 : SL(2, ℤ)) ∈ H := Subgroup.subset_closure (Or.inr (Or.inr rfl))
  refine le_antisymm ((Subgroup.closure_le _).mpr ?_) ?_
  · rintro x (rfl | rfl | rfl) <;> exact Gamma0_mem.mpr (by decide)
  · rw [← closure_schreierGens]
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨l, rfl | rfl⟩
    · have he := congrFun schreier_table_S l
      rw [he]
      fin_cases l
      · exact H.one_mem
      · exact hz
      · exact H.mul_mem (H.inv_mem hT) (H.inv_mem hU)
      · exact H.mul_mem hU hz
      · exact H.mul_mem (H.mul_mem hU hT) hz
      · exact H.inv_mem hU
    · have he := congrFun schreier_table_T l
      rw [he]
      fin_cases l
      · exact hT
      · exact H.one_mem
      · exact H.one_mem
      · exact H.one_mem
      · exact hU
      · exact H.mul_mem (H.mul_mem (H.inv_mem hU) (H.inv_mem hT)) hz

end MTT.Cohomology.GammaZeroFour

end

open scoped MatrixGroups

namespace MTT.Cohomology

theorem mem_sup_neg_one_iff (H : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) :
    g ∈ H ⊔ Subgroup.zpowers (-1) ↔ g ∈ H ∨ -g ∈ H := by
  let K : Subgroup SL(2, ℤ) :=
    { carrier := {g | g ∈ H ∨ -g ∈ H}
      one_mem' := Or.inl H.one_mem
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (H.mul_mem ha hb)
        · exact Or.inr (by simpa using H.mul_mem ha hb)
        · exact Or.inr (by simpa using H.mul_mem ha hb)
        · exact Or.inl (by simpa using H.mul_mem ha hb)
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (H.inv_mem ha)
        · exact Or.inr (by simpa using H.inv_mem ha) }
  have hle : H ⊔ Subgroup.zpowers (-1) ≤ K := by
    refine sup_le (fun _ h => Or.inl h) (Subgroup.zpowers_le.mpr ?_)
    exact Or.inr (by simpa only [neg_neg] using H.one_mem)
  refine ⟨fun h => hle h, ?_⟩
  rintro (h | h)
  · exact Subgroup.mem_sup_left h
  · have hm := Subgroup.mul_mem_sup h (Subgroup.mem_zpowers (-1 : SL(2, ℤ)))
    simpa using hm

theorem gammaOne_neg_one_not_mem_of_three_le {N : ℕ} (hN : 3 ≤ N) :
    (-1 : SL(2, ℤ)) ∉ CongruenceSubgroup.Gamma1 N := by
  intro h
  have ha := ((CongruenceSubgroup.Gamma1_mem N _).mp h).1
  have hc : ((-1 : ℤ) : ZMod N) = (1 : ℤ) := by simpa using ha
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub (-1) 1 N).mp hc
  have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt (by norm_num : (0 : ℤ) ≤ 1 - -1)
    (by omega : (1 : ℤ) - -1 < N) hd
  norm_num at hz

def gammaOneFourLower : CongruenceSubgroup.Gamma1 4 :=
  ⟨GammaZeroFour.lower, by rw [CongruenceSubgroup.Gamma1_mem]; decide⟩

theorem gammaOne_four_closure :
    Subgroup.closure ({ModularGroup.T, GammaZeroFour.lower} : Set SL(2, ℤ)) =
      CongruenceSubgroup.Gamma1 4 := by
  let H := Subgroup.closure ({ModularGroup.T, GammaZeroFour.lower} : Set SL(2, ℤ))
  have hH : H ≤ CongruenceSubgroup.Gamma1 4 := by
    apply (Subgroup.closure_le _).mpr
    rintro g (rfl | rfl)
    · exact (CongruenceSubgroup.Gamma1_mem 4 _).mpr (by decide)
    · exact gammaOneFourLower.property
  have hG : CongruenceSubgroup.Gamma0 4 ≤ H ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) := by
    rw [← GammaZeroFour.closure_T_lower_neg_one]
    apply (Subgroup.closure_le _).mpr
    rintro g (rfl | rfl | rfl)
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (Or.inl rfl))
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (Or.inr rfl))
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  refine le_antisymm hH fun g hg => ?_
  have hs := hG (CongruenceSubgroup.Gamma1_in_Gamma0 4 hg)
  rcases (mem_sup_neg_one_iff H g).mp hs with h | h
  · exact h
  · exfalso
    apply gammaOne_neg_one_not_mem_of_three_le (by decide : 3 ≤ 4)
    have hm := (CongruenceSubgroup.Gamma1 4).mul_mem (hH h)
      ((CongruenceSubgroup.Gamma1 4).inv_mem hg)
    simpa only [neg_mul, mul_inv_cancel] using hm

end MTT.Cohomology

/-! # Eta-product transformations at level four

Adapted from Claude's accepted Prove2Me proof 9f9d7099-dd4e-5af0-8131-7c3e5d2d1482,
itself transplanted from anthropics/fermats-last-theorem commit
aa2d8b34692b16c70f699536de0d8e75b9a3e9ef. Only the elementary analytic identities
are reused. Resource overrides, utility macros and its even-weight restriction
are not imported. The final application is on Gamma1(4), using two generators.
-/

noncomputable section

open scoped MatrixGroups ModularForm Real UpperHalfPlane
open ModularGroup Complex
open ModularForm (eta eta_q eta_q_eq_cexp)

namespace MTT.Cohomology.EtaFour

def Fc (a b c : ℕ) (w : ℂ) : ℂ := η w ^ a * η (2 * w) ^ b * η (4 * w) ^ c

def F (a b c : ℕ) (z : ℍ) : ℂ := Fc a b c z

def Gc (a b c : ℕ) (w : ℂ) : ℂ := η w ^ a * η (w / 2) ^ b * η (w / 4) ^ c

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

lemma cexp_phase_eq_one (s : ℤ) (h : (24 : ℤ) ∣ s) : cexp (π * I * s / 12) = 1 := by
  obtain ⟨t, rfl⟩ := h
  have : (π * I * ((24 * t : ℤ) : ℂ) / 12) = t * (2 * π * I) := by push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

lemma Fc_add_int (a b c : ℕ) (w : ℂ) (m : ℤ) :
    Fc a b c (w + m) =
      cexp (π * I * ((m * (a + 2 * b + 4 * c : ℕ) : ℤ) : ℂ) / 12) * Fc a b c w := by
  unfold Fc
  have h2 : 2 * (w + m) = 2 * w + ((2 * m : ℤ) : ℂ) := by push_cast; ring
  have h4 : 4 * (w + m) = 4 * w + ((4 * m : ℤ) : ℂ) := by push_cast; ring
  rw [h2, h4, eta_add_int_pow, eta_add_int_pow, eta_add_int_pow]
  have : cexp (π * I * (m * a) / 12) * η w ^ a *
      (cexp (π * I * (((2 * m : ℤ) : ℂ) * b) / 12) * η (2 * w) ^ b) *
      (cexp (π * I * (((4 * m : ℤ) : ℂ) * c) / 12) * η (4 * w) ^ c) =
      (cexp (π * I * (m * a) / 12) * cexp (π * I * (((2 * m : ℤ) : ℂ) * b) / 12) *
        cexp (π * I * (((4 * m : ℤ) : ℂ) * c) / 12)) *
        (η w ^ a * η (2 * w) ^ b * η (4 * w) ^ c) := by ring
  rw [this, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  push_cast
  ring

lemma Gc_add_four_mul_int (a b c : ℕ) (w : ℂ) (m : ℤ) :
    Gc a b c (w + ((4 * m : ℤ) : ℂ)) =
      cexp (π * I * ((m * (4 * a + 2 * b + c : ℕ) : ℤ) : ℂ) / 12) * Gc a b c w := by
  unfold Gc
  have h2 : (w + ((4 * m : ℤ) : ℂ)) / 2 = w / 2 + ((2 * m : ℤ) : ℂ) := by push_cast; ring
  have h4 : (w + ((4 * m : ℤ) : ℂ)) / 4 = w / 4 + ((m : ℤ) : ℂ) := by push_cast; ring
  rw [h2, h4, eta_add_int_pow, eta_add_int_pow, eta_add_int_pow]
  have : cexp (π * I * (((4 * m : ℤ) : ℂ) * a) / 12) * η w ^ a *
      (cexp (π * I * (((2 * m : ℤ) : ℂ) * b) / 12) * η (w / 2) ^ b) *
      (cexp (π * I * ((m : ℂ) * c) / 12) * η (w / 4) ^ c) =
      (cexp (π * I * (((4 * m : ℤ) : ℂ) * a) / 12) *
        cexp (π * I * (((2 * m : ℤ) : ℂ) * b) / 12) *
        cexp (π * I * ((m : ℂ) * c) / 12)) *
        (η w ^ a * η (w / 2) ^ b * η (w / 4) ^ c) := by ring
  rw [this, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  push_cast
  ring

lemma Fc_add_one (a b c : ℕ) (h₁ : 24 ∣ a + 2 * b + 4 * c) (w : ℂ) :
    Fc a b c (w + 1) = Fc a b c w := by
  have := Fc_add_int a b c w 1
  rw [Int.cast_one] at this
  rw [this, cexp_phase_eq_one _ (by rw [one_mul]; exact Int.natCast_dvd_natCast.mpr h₁), one_mul]

lemma Gc_sub_four (a b c : ℕ) (h₂ : 24 ∣ 4 * a + 2 * b + c) (w : ℂ) :
    Gc a b c (w + ((-4 : ℤ) : ℂ)) = Gc a b c w := by
  have := Gc_add_four_mul_int a b c w (-1)
  rw [show ((4 * (-1 : ℤ) : ℤ)) = -4 by norm_num] at this
  rw [this, cexp_phase_eq_one _ ?_, one_mul]
  rw [neg_mul, one_mul, dvd_neg]
  exact Int.natCast_dvd_natCast.mpr h₂

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

def CS (a' b' c' : ℕ) : ℂ :=
  (I⁻¹) ^ (a' + b' + c') * (2⁻¹ : ℂ) ^ b' * (4⁻¹ : ℂ) ^ c'

lemma Fc_neg_inv (a' b' c' : ℕ) (z : ℂ) (hz : 0 < z.im) :
    Fc (2 * a') (2 * b') (2 * c') (-z⁻¹) =
      CS a' b' c' * z ^ (a' + b' + c') * Gc (2 * a') (2 * b') (2 * c') z := by
  unfold Fc Gc CS
  have h2 : 2 * -z⁻¹ = -(z / 2)⁻¹ := by rw [inv_div]; ring
  have h4 : 4 * -z⁻¹ = -(z / 4)⁻¹ := by rw [inv_div]; ring
  have hz2 : 0 < (z / 2).im := by rw [Complex.div_ofNat_im]; positivity
  have hz4 : 0 < (z / 4).im := by rw [Complex.div_ofNat_im]; positivity
  rw [h2, h4, eta_neg_inv_pow z hz, eta_neg_inv_pow _ hz2, eta_neg_inv_pow _ hz4]
  ring

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

lemma F_slash_S (a' b' c' : ℕ) :
    (F (2 * a') (2 * b') (2 * c')) ∣[((a' + b' + c' : ℕ) : ℤ)] ModularGroup.S =
      fun z : ℍ => CS a' b' c' * Gc (2 * a') (2 * b') (2 * c') z := by
  ext z
  rw [ModularForm.SL_slash_apply, denom_S, F, coe_S_smul,
    Fc_neg_inv _ _ _ _ z.im_pos, zpow_neg, zpow_natCast]
  have hz : (z : ℂ) ^ (a' + b' + c') ≠ 0 := pow_ne_zero _ z.ne_zero
  field_simp

lemma F_slash_S_slash_T (a' b' c' : ℕ) (h₂ : 24 ∣ 4 * (2 * a') + 2 * (2 * b') + 2 * c') :
    ((F (2 * a') (2 * b') (2 * c')) ∣[((a' + b' + c' : ℕ) : ℤ)] ModularGroup.S)
      ∣[((a' + b' + c' : ℕ) : ℤ)] (ModularGroup.T ^ (-4 : ℤ)) =
      (F (2 * a') (2 * b') (2 * c')) ∣[((a' + b' + c' : ℕ) : ℤ)] ModularGroup.S := by
  rw [F_slash_S]
  ext z
  rw [ModularForm.SL_slash_apply, denom_T_zpow, one_zpow, mul_one, coe_T_zpow_smul]
  rw [Gc_sub_four _ _ _ h₂]

lemma coe_T_smul (z : ℍ) : ((ModularGroup.T • z : ℍ) : ℂ) = (z : ℂ) + 1 := by
  rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd]; push_cast; ring

lemma denom_T (z : ℍ) :
    UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) ModularGroup.T)) (z : ℂ) = 1 := by
  rw [denom_SL]; simp [ModularGroup.coe_T]

lemma F_slash_T (a b c : ℕ) (k : ℤ) (h₁ : 24 ∣ a + 2 * b + 4 * c) :
    (F a b c) ∣[k] ModularGroup.T = F a b c := by
  ext z
  rw [ModularForm.SL_slash_apply, denom_T, one_zpow, mul_one, F, F,
    coe_T_smul, Fc_add_one _ _ _ h₁]

lemma F_mdifferentiable (a b c : ℕ) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (F a b c) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hFc : DifferentiableOn ℂ (Fc a b c) {z : ℂ | 0 < z.im} := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    have hz' : 0 < z.im := hz
    have h2 : 0 < (2 * z).im := by simp [Complex.mul_im]; positivity
    have h4 : 0 < (4 * z).im := by simp [Complex.mul_im]; positivity
    unfold Fc
    refine ((ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hz').pow _ |>.mul
      (((ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet h2).comp z
        (differentiableAt_id.const_mul _)).pow _)).mul
      (((ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet h4).comp z
        (differentiableAt_id.const_mul _)).pow _)
  refine hFc.congr fun z hz => ?_
  have hz' : 0 < z.im := hz
  simp [F, Function.comp, UpperHalfPlane.ofComplex_apply_of_im_pos hz']

end MTT.Cohomology.EtaFour

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

/-! # A nonzero weight-five cusp form on Gamma1(4) -/

section

open UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace MTT.Cohomology

open EtaFour

theorem eta_weight_five_slash_lower :
    F 4 2 4 ∣[(5 : ℤ)] GammaZeroFour.lower = F 4 2 4 := by
  have ht := F_slash_S_slash_T 2 1 2 (by decide)
  change (F 4 2 4 ∣[(5 : ℤ)] ModularGroup.S) ∣[(5 : ℤ)]
    (ModularGroup.T ^ (-4 : ℤ)) = F 4 2 4 ∣[(5 : ℤ)] ModularGroup.S at ht
  have ht4 : (F 4 2 4 ∣[(5 : ℤ)] ModularGroup.S) ∣[(5 : ℤ)]
      (ModularGroup.T ^ (4 : ℤ)) = F 4 2 4 ∣[(5 : ℤ)] ModularGroup.S := by
    have h := congrArg (fun f : UpperHalfPlane → ℂ =>
      f ∣[(5 : ℤ)] (ModularGroup.T ^ (4 : ℤ))) ht
    simpa only [← SlashAction.slash_mul, mul_assoc, ← _root_.zpow_add, Int.reduceAdd,
      zpow_zero, mul_one] using h.symm
  have hu : GammaZeroFour.lower =
      ModularGroup.S * ModularGroup.T ^ (4 : ℤ) * ModularGroup.S⁻¹ := by
    decide
  rw [hu, SlashAction.slash_mul, SlashAction.slash_mul, ht4,
    ← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]

theorem eta_weight_five_slash_eq :
    ∀ γ ∈ MTT.GammaOne 4, F 4 2 4 ∣[(5 : ℤ)] γ = F 4 2 4 := by
  have hΓ : MTT.GammaOne 4 = Subgroup.closure
      ((Matrix.SpecialLinearGroup.mapGL ℝ) ''
        ({ModularGroup.T, GammaZeroFour.lower} : Set SL(2, ℤ))) := by
    change (CongruenceSubgroup.Gamma1 4).map _ = _
    rw [← gammaOne_four_closure, MonoidHom.map_closure]
  rw [SlashInvariantForm.slash_action_generators hΓ]
  rintro _ ⟨γ, hγ, rfl⟩
  rcases hγ with rfl | rfl
  · exact F_slash_T 4 2 4 5 (by decide)
  · exact eta_weight_five_slash_lower

theorem exists_eta_weight_ten :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 4) 10,
      (g : UpperHalfPlane → ℂ) = F 4 2 4 * F 4 2 4 := by
  obtain ⟨g, hg⟩ := CuspForm.exists_gamma0_four_apply_eq_eta_pow_mul
    8 4 8 (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨g, ?_⟩
  funext z
  rw [hg]
  simp only [Pi.mul_apply, F, Fc]
  ring

theorem eta_weight_five_zero_at {c : OnePoint ℝ} (hc : IsCusp c (MTT.GammaOne 4)) :
    c.IsZeroAt (F 4 2 4) 5 := by
  obtain ⟨g, hg⟩ := exists_eta_weight_ten
  have hlevel : MTT.GammaOne 4 ≤
      (CongruenceSubgroup.Gamma0 4 : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.map_mono (CongruenceSubgroup.Gamma1_in_Gamma0 4)
  apply OnePoint.IsZeroAt.of_mul_self (k := 5)
    ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z (MTT.GammaOne 4)).mp hc)
  rw [show (5 : ℤ) + 5 = 10 by norm_num, ← hg]
  exact g.zero_at_cusps' (hc.mono hlevel)

theorem exists_weight_five_cusp_seed_level_four :
    ∃ D : CuspForm (MTT.GammaOne 4) 5, D ≠ 0 := by
  let D : CuspForm (MTT.GammaOne 4) 5 :=
    { toFun := F 4 2 4
      slash_action_eq' := eta_weight_five_slash_eq
      holo' := F_mdifferentiable 4 2 4
      zero_at_cusps' := eta_weight_five_zero_at }
  refine ⟨D, ?_⟩
  intro hd
  have hz := congrArg (fun g : CuspForm (MTT.GammaOne 4) 5 => g I) hd
  have he : F 4 2 4 I ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero (pow_ne_zero _ (ModularForm.eta_ne_zero I.im_pos))
      (pow_ne_zero _ (ModularForm.eta_ne_zero ?_)))
      (pow_ne_zero _ (ModularForm.eta_ne_zero ?_))
    all_goals norm_num [Complex.mul_im]
  exact he hz

end MTT.Cohomology

theorem solution : ∃ D : CuspForm (MTT.GammaOne 4) 5, D ≠ 0 :=
  MTT.Cohomology.exists_weight_five_cusp_seed_level_four
