import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Tactic.NormNum.IsCoprime

import Definitions.MTT.Def_MTT_Arithmetic
import Theorems.FLT.Thm_ModularForm_exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd

noncomputable section

section GammaZeroFourGenerators

/-! # A six-coset Schreier computation for Gamma0(4)

The transversal argument follows the platform's level-three generator proof
by adapting its row-label calculation to the nonfield ZMod 4.
-/

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

end GammaZeroFourGenerators

section WeightOneFourSeed

/-! # The quadratic weight-one Eisenstein series at level four -/


open UpperHalfPlane
open scoped MatrixGroups

namespace MTT.Cohomology

def chiFour : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

theorem chiFour_apply_neg_one : chiFour (-1) = -1 := by
  rw [show (-1 : ZMod 4) = 3 by decide]
  change ((-1 : ℤ) : ℂ) = -1
  norm_num

theorem chiFour_isPrimitive : chiFour.IsPrimitive := by
  have hd := chiFour.conductor_dvd_level
  have hc : chiFour.conductor = 1 ∨ chiFour.conductor = 2 ∨ chiFour.conductor = 4 := by
    have hb := Nat.le_of_dvd (by decide : 0 < 4) hd
    interval_cases h : chiFour.conductor <;> simp_all
  rcases hc with hc | hc | hc
  · have he := chiFour.primitiveCharacter_apply_of_isCoprime
      (a := -1) (by norm_num : IsCoprime (-1 : ℤ) (4 : ℤ))
    have hs : ((-1 : ℤ) : ZMod chiFour.conductor) = (1 : ℤ) := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      norm_num [hc]
    rw [hs, Int.cast_one, map_one, Int.cast_neg, Int.cast_one,
      chiFour_apply_neg_one] at he
    norm_num at he
  · have he := chiFour.primitiveCharacter_apply_of_isCoprime
      (a := -1) (by norm_num : IsCoprime (-1 : ℤ) (4 : ℤ))
    have hs : ((-1 : ℤ) : ZMod chiFour.conductor) = (1 : ℤ) := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      norm_num [hc]
    rw [hs, Int.cast_one, map_one, Int.cast_neg, Int.cast_one,
      chiFour_apply_neg_one] at he
    norm_num at he
  · exact hc

theorem exists_weight_one_four_coefficients :
    ∃ A : ModularForm (MTT.GammaOne 4) 1,
      (qExpansion 1 A).coeff 0 = (1 / 4 : ℂ) ∧
      (qExpansion 1 A).coeff 1 = 1 ∧
      ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 4 → ∀ z : UpperHalfPlane,
        A (γ • z) = chiFour (γ 1 1) *
          ((((γ 1 0 : ℤ) : ℂ) * (z : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ (1 : ℤ) * A z) := by
  obtain ⟨A, hslash, hzero, hcoeff⟩ :=
    ModularForm.exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd
      4 chiFour chiFour_isPrimitive chiFour_apply_neg_one
  refine ⟨A, ?_, ?_, hslash⟩
  · change ModularFormClass.qCoeff A 0 = _
    rw [hzero]
    norm_num [Finset.sum_range_succ, chiFour, MulChar.ringHomComp_apply, ZMod.χ₄]
  · change ModularFormClass.qCoeff A 1 = _
    rw [hcoeff 1 (by decide)]
    norm_num [chiFour, MulChar.ringHomComp_apply, ZMod.χ₄]

theorem exists_weight_one_seed_level_four :
    ∃ A : ModularForm (MTT.GammaOne 4) 1, PowerSeries.order (qExpansion 1 A) = 0 := by
  obtain ⟨A, hzero, _, _⟩ := exists_weight_one_four_coefficients
  refine ⟨A, PowerSeries.order_eq_nat.mpr ⟨?_, ?_⟩⟩
  · rw [hzero]
    norm_num
  · intro i hi
    exact (Nat.not_lt_zero i hi).elim

end MTT.Cohomology

end WeightOneFourSeed

section WeightTwoFourSquare

/-! # Squaring the quadratic weight-one Eisenstein series -/


open UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace MTT.Cohomology

theorem chiFour_sq_of_isUnit {a : ZMod 4} (ha : IsUnit a) : chiFour a ^ 2 = 1 := by
  have hq : chiFour.IsQuadratic := ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)
  have h := congrArg (fun χ : DirichletCharacter ℂ 4 => χ a) hq.sq_eq_one
  rw [chiFour.pow_apply' (by decide) a, MulChar.one_apply ha] at h
  exact h

theorem gammaZeroFour_d_isUnit (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 4) :
    IsUnit (γ 1 1 : ZMod 4) := by
  have hc := CongruenceSubgroup.Gamma0_mem.mp hγ
  have hd : (γ 0 0 : ZMod 4) * (γ 1 1 : ZMod 4) = 1 := by
    have hz := γ.property
    rw [Matrix.det_fin_two] at hz
    have h := congrArg (Int.castRingHom (ZMod 4)) hz
    simpa only [map_sub, map_mul, map_one, Int.coe_castRingHom, hc, mul_zero, sub_zero] using h
  exact isUnit_iff_exists_inv'.mpr ⟨(γ 0 0 : ZMod 4), hd⟩

theorem exists_weight_two_four_coefficients :
    ∃ F : ModularForm (CongruenceSubgroup.Gamma0 4) 2,
      (qExpansion 1 F).coeff 0 = (1 / 16 : ℂ) ∧
      (qExpansion 1 F).coeff 1 = (1 / 2 : ℂ) := by
  obtain ⟨A, hzero, hone, hslash⟩ := exists_weight_one_four_coefficients
  let F₁ : ModularForm (MTT.GammaOne 4) 2 := A.mul A
  have heq : (F₁ : UpperHalfPlane → ℂ) = fun z => A z * A z := rfl
  have hmod : ∀ γ ∈ (CongruenceSubgroup.Gamma0 4 : Subgroup (GL (Fin 2) ℝ)),
      (F₁ : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] γ = F₁ := by
    rintro _ ⟨γ, hγ, rfl⟩
    funext z
    apply (ModularForm.slash_action_eq'_iff 2 F₁ γ z).mpr
    rw [show F₁ (γ • z) = A (γ • z) * A (γ • z) from rfl,
      show F₁ z = A z * A z from rfl, hslash γ hγ z]
    have hs := chiFour_sq_of_isUnit (gammaZeroFour_d_isUnit γ hγ)
    simp only [zpow_ofNat]
    calc
      _ = chiFour (γ 1 1) ^ 2 *
          (((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ)) ^ 2 * (A z * A z) := by ring
      _ = _ := by rw [hs, one_mul]
  let F : ModularForm (CongruenceSubgroup.Gamma0 4) 2 :=
    { toFun := F₁
      slash_action_eq' := hmod
      holo' := F₁.holo'
      bdd_at_cusps' := fun hc => F₁.bdd_at_cusps'
        ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z (MTT.GammaOne 4)).mpr
          ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z
            (CongruenceSubgroup.Gamma0 4 : Subgroup (GL (Fin 2) ℝ))).mp hc)) }
  have hΓ : (1 : ℝ) ∈ (MTT.GammaOne 4).strictPeriods := by
    change (1 : ℝ) ∈ (CongruenceSubgroup.Gamma1 4 : Subgroup (GL (Fin 2) ℝ)).strictPeriods
    rw [CongruenceSubgroup.strictPeriods_Gamma1]
    exact AddSubgroup.mem_zmultiples 1
  have hq : qExpansion 1 F = qExpansion 1 A * qExpansion 1 A :=
    ModularForm.qExpansion_mul (by norm_num) hΓ A A
  refine ⟨F, ?_, ?_⟩
  · rw [hq, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff, hzero]
    norm_num
  · rw [hq, PowerSeries.coeff_one_mul, ← PowerSeries.coeff_zero_eq_constantCoeff, hzero, hone]
    norm_num

end MTT.Cohomology

end WeightTwoFourSquare

section HalfTranslationFour

/-! # Half-translation at level four -/


open UpperHalfPlane
open scoped MatrixGroups ModularForm Pointwise

namespace MTT.Cohomology

def halfTranslation : GL (Fin 2) ℝ :=
  ⟨!![1, 1 / 2; 0, 1], !![1, -1 / 2; 0, 1], by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem halfTranslation_det : (halfTranslation.det : ℝ) = 1 := by
  norm_num [Matrix.GeneralLinearGroup.val_det_apply, halfTranslation, Matrix.det_fin_two]

theorem halfTranslation_apply (z : UpperHalfPlane) :
    ((halfTranslation • z : UpperHalfPlane) : ℂ) = (z : ℂ) + 1 / 2 := by
  rw [coe_smul_of_det_pos (by rw [halfTranslation_det]; norm_num)]
  norm_num [num, denom, halfTranslation]

theorem slash_halfTranslation (f : UpperHalfPlane → ℂ) (k : ℤ) :
    f ∣[k] halfTranslation = fun z => f (halfTranslation • z) := by
  funext z
  rw [ModularForm.slash_def, halfTranslation_det]
  norm_num [σ, halfTranslation_det, denom, halfTranslation]

theorem halfTranslation_conj_T :
    halfTranslation * Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T * halfTranslation⁻¹ =
      Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;>
    norm_num [halfTranslation, ModularGroup.T, Matrix.map, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.vecHead, Matrix.vecTail]

def halfLower : SL(2, ℤ) := ⟨!![-1, 1; -4, 3], by decide⟩

theorem halfTranslation_conj_lower :
    halfTranslation * Matrix.SpecialLinearGroup.mapGL ℝ GammaZeroFour.lower *
        halfTranslation⁻¹ = Matrix.SpecialLinearGroup.mapGL ℝ halfLower := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;>
    norm_num [halfTranslation, GammaZeroFour.lower, halfLower,
      Matrix.map, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail]

theorem gammaZeroFour_le_half_conj :
    (CongruenceSubgroup.Gamma0 4 : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct halfTranslation⁻¹ •
        (CongruenceSubgroup.Gamma0 4 : Subgroup (GL (Fin 2) ℝ)) := by
  have hΓ : (CongruenceSubgroup.Gamma0 4 : Subgroup (GL (Fin 2) ℝ)) =
      Subgroup.closure ((Matrix.SpecialLinearGroup.mapGL ℝ) ''
        ({ModularGroup.T, GammaZeroFour.lower, -1} : Set SL(2, ℤ))) := by
    rw [← GammaZeroFour.closure_T_lower_neg_one, MonoidHom.map_closure]
  rw [hΓ]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨γ, hγ, rfl⟩
  rw [← hΓ]
  change Matrix.SpecialLinearGroup.mapGL ℝ γ ∈
    (ConjAct.toConjAct halfTranslation⁻¹ •
      (CongruenceSubgroup.Gamma0 4 : Subgroup (GL (Fin 2) ℝ)))
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  change halfTranslation * Matrix.SpecialLinearGroup.mapGL ℝ γ * halfTranslation⁻¹ ∈ _
  rcases hγ with rfl | rfl | rfl
  · rw [halfTranslation_conj_T]
    exact Subgroup.mem_map_of_mem _ (CongruenceSubgroup.Gamma0_mem.mpr (by decide))
  · rw [halfTranslation_conj_lower]
    exact Subgroup.mem_map_of_mem _ (CongruenceSubgroup.Gamma0_mem.mpr (by decide))
  · have he : halfTranslation * Matrix.SpecialLinearGroup.mapGL ℝ (-1 : SL(2, ℤ)) *
        halfTranslation⁻¹ = Matrix.SpecialLinearGroup.mapGL ℝ (-1 : SL(2, ℤ)) := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        norm_num [halfTranslation, Matrix.mul_apply, Fin.sum_univ_two]
    rw [he]
    exact Subgroup.mem_map_of_mem _ (CongruenceSubgroup.Gamma0_mem.mpr (by decide))

def halfTranslate (F : ModularForm (CongruenceSubgroup.Gamma0 4) 2) :
    ModularForm (CongruenceSubgroup.Gamma0 4) 2 :=
  { toFun := ModularForm.translate F halfTranslation
    slash_action_eq' := fun γ hγ =>
      (ModularForm.translate F halfTranslation).slash_action_eq' γ (gammaZeroFour_le_half_conj hγ)
    holo' := (ModularForm.translate F halfTranslation).holo'
    bdd_at_cusps' := fun hc =>
      (ModularForm.translate F halfTranslation).bdd_at_cusps' (hc.mono gammaZeroFour_le_half_conj) }

theorem halfTranslate_apply (F : ModularForm (CongruenceSubgroup.Gamma0 4) 2)
    (z : UpperHalfPlane) : halfTranslate F z = F (halfTranslation • z) :=
  congrFun (slash_halfTranslation F 2) z

end MTT.Cohomology

end HalfTranslationFour

section HalfTranslationQExpansion

/-! # Coefficients under half-translation -/


open UpperHalfPlane
open scoped MatrixGroups

namespace MTT.Cohomology

theorem qParam_halfTranslation (z : UpperHalfPlane) :
    Function.Periodic.qParam 1 (halfTranslation • z : UpperHalfPlane) =
      -Function.Periodic.qParam 1 z := by
  simp only [Function.Periodic.qParam, halfTranslation_apply, Complex.ofReal_one, div_one]
  rw [show (2 * Real.pi * Complex.I * ((z : ℂ) + 1 / 2) : ℂ) =
      2 * Real.pi * Complex.I * z + Real.pi * Complex.I by ring,
    Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]

theorem qExpansion_halfTranslate_coeff (F : ModularForm (CongruenceSubgroup.Gamma0 4) 2)
    (n : ℕ) :
    (qExpansion 1 (halfTranslate F)).coeff n = (-1 : ℂ) ^ n * (qExpansion 1 F).coeff n := by
  have hΓ : (1 : ℝ) ∈
      (CongruenceSubgroup.Gamma0 4 : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma0]
    exact AddSubgroup.mem_zmultiples 1
  symm
  refine ModularFormClass.qExpansion_coeff_unique (f := halfTranslate F)
    (c := fun m => (-1 : ℂ) ^ m * (qExpansion 1 F).coeff m) (by norm_num) hΓ ?_ n
  intro z
  have h := ModularForm.hasSum_qExpansion F (by norm_num) hΓ (halfTranslation • z)
  rw [← halfTranslate_apply] at h
  apply h.congr_fun
  intro m
  change ((-1 : ℂ) ^ m * (qExpansion 1 F).coeff m) * Function.Periodic.qParam 1 z ^ m =
    (qExpansion 1 F).coeff m *
      Function.Periodic.qParam 1 (halfTranslation • z : UpperHalfPlane) ^ m
  rw [qParam_halfTranslation, neg_pow]
  ring

end MTT.Cohomology

end HalfTranslationQExpansion

section LevelFourModularPair

/-! # The low-weight modular pair at level four -/


open UpperHalfPlane
open scoped MatrixGroups

namespace MTT.Cohomology

theorem exists_weight_two_seed_level_four :
    ∃ B : ModularForm (MTT.GammaOne 4) 2, PowerSeries.order (qExpansion 1 B) = 1 := by
  obtain ⟨F, hzero, hone⟩ := exists_weight_two_four_coefficients
  let B₀ := F - halfTranslate F
  have hΓ : (1 : ℝ) ∈
      (CongruenceSubgroup.Gamma0 4 : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma0]
    exact AddSubgroup.mem_zmultiples 1
  have hc (n : ℕ) : (qExpansion 1 B₀).coeff n =
      (qExpansion 1 F).coeff n - (-1 : ℂ) ^ n * (qExpansion 1 F).coeff n := by
    change (qExpansion 1 ((F : UpperHalfPlane → ℂ) - halfTranslate F)).coeff n = _
    rw [ModularForm.qExpansion_sub (by norm_num) hΓ F (halfTranslate F), map_sub,
      qExpansion_halfTranslate_coeff]
  have ho : PowerSeries.order (qExpansion 1 B₀) = 1 := by
    apply PowerSeries.order_eq_nat.mpr
    constructor
    · rw [hc 1, hone]
      norm_num
    · intro i hi
      have : i = 0 := by omega
      subst i
      rw [hc 0]
      ring
  have hlevel : MTT.GammaOne 4 ≤
      (CongruenceSubgroup.Gamma0 4 : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.map_mono (CongruenceSubgroup.Gamma1_in_Gamma0 4)
  let B : ModularForm (MTT.GammaOne 4) 2 :=
    { toFun := B₀
      slash_action_eq' := fun γ hγ => B₀.slash_action_eq' γ (hlevel hγ)
      holo' := B₀.holo'
      bdd_at_cusps' := fun hc => B₀.bdd_at_cusps' (hc.mono hlevel) }
  exact ⟨B, ho⟩

theorem exists_weighted_modular_seeds_level_four_aux :
    ∃ A : ModularForm (MTT.GammaOne 4) 1,
      ∃ B : ModularForm (MTT.GammaOne 4) 2,
        MvPowerSeries.order (qExpansion 1 A) = 0 ∧
          MvPowerSeries.order (qExpansion 1 B) = 1 := by
  obtain ⟨A, hA⟩ := exists_weight_one_seed_level_four
  obtain ⟨B, hB⟩ := exists_weight_two_seed_level_four
  exact ⟨A, B, PowerSeries.order_eq_order.symm.trans hA,
    PowerSeries.order_eq_order.symm.trans hB⟩

end MTT.Cohomology

end LevelFourModularPair

theorem solution :
    ∃ A : ModularForm (MTT.GammaOne 4) 1,
      ∃ B : ModularForm (MTT.GammaOne 4) 2,
        MvPowerSeries.order (UpperHalfPlane.qExpansion 1 A) = 0 ∧
          MvPowerSeries.order (UpperHalfPlane.qExpansion 1 B) = 1 :=
  MTT.Cohomology.exists_weighted_modular_seeds_level_four_aux
