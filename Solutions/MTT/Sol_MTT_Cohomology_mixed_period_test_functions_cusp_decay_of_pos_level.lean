/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Definitions.MTT.Def_MTT_Cohomology
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Definitions.MTT.Def_MTT_PeriodPairing
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Definitions.MTT.Def_MTT_ParabolicCohomology
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Field.Periodic
import Theorems.MTT.Thm_MTT_Cohomology_mixed_period_test_functions_local_equivariant

noncomputable section

section Part0

/-! # Finite coordinates for binary homogeneous polynomials -/


namespace MTT.Cohomology

def homogeneousExponentEquiv (n : ℕ) :
    {d : Fin 2 →₀ ℕ // d.degree = n} ≃ Fin (n + 1) where
  toFun d := ⟨d.val 0, by
    have hd := d.property
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hd
    omega⟩
  invFun j := ⟨Finsupp.equivFunOnFinite.symm ![j.val, n - j.val], by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
    change j.val + (n - j.val) = n
    omega⟩
  left_inv d := by
    apply Subtype.ext
    ext i
    have hd := d.property
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hd
    change (![d.val 0, n - d.val 0] : Fin 2 → ℕ) i = d.val i
    fin_cases i
    · rfl
    · change n - d.val 0 = d.val 1
      omega
  right_inv j := by
    apply Fin.ext
    rfl

def symmetricPowerCoordinates (R : Type*) [CommRing R] (n : ℕ) :
    Sym R n ≃ₗ[R] (Fin (n + 1) →₀ R) :=
  (LinearEquiv.ofEq _ _ (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (Fin 2) R n))
    ≪≫ₗ AddMonoidAlgebra.supportedEquivFinsupp _
    ≪≫ₗ Finsupp.domLCongr (homogeneousExponentEquiv n)

def symmetricPowerBasis (R : Type*) [CommRing R] (n : ℕ) :
    Module.Basis (Fin (n + 1)) R (Sym R n) :=
  Module.Basis.ofRepr (symmetricPowerCoordinates R n)

@[simp]
theorem symmetricPowerBasis_repr (R : Type*) [CommRing R] (n : ℕ) :
    (symmetricPowerBasis R n).repr = symmetricPowerCoordinates R n := rfl

theorem symmetricPowerCoordinates_apply {R : Type*} [CommRing R] {n : ℕ}
    (P : Sym R n) (j : Fin (n + 1)) :
    symmetricPowerCoordinates R n P j =
      AddMonoidAlgebra.coeff P.val (homogeneousExponentEquiv n |>.symm j).val := by
  rfl

theorem symmetricPowerBasis_val {R : Type*} [CommRing R] {n : ℕ} (j : Fin (n + 1)) :
    (symmetricPowerBasis R n j).val =
      MvPolynomial.monomial (homogeneousExponentEquiv n |>.symm j).val 1 := by
  classical
  let Q : Sym R n := ⟨MvPolynomial.monomial ((homogeneousExponentEquiv n).symm j).val 1,
    MvPolynomial.isHomogeneous_monomial 1 ((homogeneousExponentEquiv n).symm j).property⟩
  have h : symmetricPowerBasis R n j = Q := by
    apply (symmetricPowerCoordinates R n).injective
    ext i
    change (symmetricPowerBasis R n).repr (symmetricPowerBasis R n j) i = _
    rw [Module.Basis.repr_self_apply, symmetricPowerCoordinates_apply]
    simp [Q, MvPolynomial.coeff_monomial, Subtype.val_inj]
  exact congrArg Subtype.val h

theorem symmetricPowerBasis_val_eq {R : Type*} [CommRing R] {n : ℕ}
    (j : Fin (n + 1)) : (symmetricPowerBasis R n j).val =
      MvPolynomial.X 0 ^ j.val * MvPolynomial.X 1 ^ (n - j.val) := by
  rw [symmetricPowerBasis_val, MvPolynomial.monomial_eq]
  simp [homogeneousExponentEquiv, Finsupp.prod_fintype, Fin.prod_univ_two]

theorem symmetricPower_expansion {R : Type*} [CommRing R] {n : ℕ} (P : Sym R n) :
    P.val = ∑ j : Fin (n + 1), symmetricPowerCoordinates R n P j •
      (MvPolynomial.X 0 ^ j.val * MvPolynomial.X 1 ^ (n - j.val)) := by
  have h := congrArg Subtype.val ((symmetricPowerBasis R n).sum_repr P)
  simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower, symmetricPowerBasis_val_eq,
    symmetricPowerBasis_repr]
    using h.symm

end MTT.Cohomology

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
        MvPolynomial.C_mul_monomial, MvPolynomial.monomial_mul,
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

end MTT.PeriodMeasure

end Part1

section Part2
/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

/-! # Polynomial coefficient growth in integral cusp charts -/

set_option autoImplicit false
open UpperHalfPlane Complex Filter
open scoped Topology BigOperators MatrixGroups Modular ComplexConjugate

namespace MTT.CuspDecay

/-- A polynomial bound on the part of a vertical strip above height one. -/
def StripGrowth (W : ℝ) (f : ℍ → ℂ) : Prop :=
  ∃ (C : ℝ) (n : ℕ), 0 ≤ C ∧ ∀ z : ℍ, 1 ≤ z.im → |z.re| ≤ W →
    ‖f z‖ ≤ C * (1 + z.im) ^ n

namespace StripGrowth

variable {W : ℝ} {f g : ℍ → ℂ}

theorem const (c : ℂ) : StripGrowth W (fun _ => c) :=
  ⟨‖c‖, 0, norm_nonneg _, fun _ _ _ => by simp⟩

theorem add (hf : StripGrowth W f) (hg : StripGrowth W g) :
    StripGrowth W (fun z => f z + g z) := by
  obtain ⟨C, n, hC, hf⟩ := hf
  obtain ⟨D, m, hD, hg⟩ := hg
  refine ⟨C + D, n + m, add_nonneg hC hD, fun z hz hw => ?_⟩
  have hy : 1 ≤ 1 + z.im := by linarith [z.im_pos]
  calc
    _ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
    _ ≤ C * (1 + z.im) ^ n + D * (1 + z.im) ^ m := add_le_add (hf z hz hw) (hg z hz hw)
    _ ≤ C * (1 + z.im) ^ (n + m) + D * (1 + z.im) ^ (n + m) := by
      gcongr <;> omega
    _ = _ := by ring

theorem mul (hf : StripGrowth W f) (hg : StripGrowth W g) :
    StripGrowth W (fun z => f z * g z) := by
  obtain ⟨C, n, hC, hf⟩ := hf
  obtain ⟨D, m, hD, hg⟩ := hg
  refine ⟨C * D, n + m, mul_nonneg hC hD, fun z hz hw => ?_⟩
  rw [norm_mul]
  calc
    _ ≤ (C * (1 + z.im) ^ n) * (D * (1 + z.im) ^ m) :=
      mul_le_mul (hf z hz hw) (hg z hz hw) (norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

theorem conjugate (hf : StripGrowth W f) : StripGrowth W (fun z => conj (f z)) := by
  simpa only [StripGrowth, Complex.norm_conj] using hf

theorem pow (hf : StripGrowth W f) (n : ℕ) : StripGrowth W (fun z => f z ^ n) := by
  induction n with
  | zero => simpa using (const (W := W) 1)
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem sum {ι : Type*} (s : Finset ι) (f : ι → ℍ → ℂ)
    (hf : ∀ i ∈ s, StripGrowth W (f i)) : StripGrowth W (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const (W := W) 0)
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self _ _)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem coe (hW : 0 ≤ W) : StripGrowth W (fun z => (z : ℂ)) := by
  refine ⟨W + 1, 1, by positivity, fun z hz hw => ?_⟩
  calc
    ‖(z : ℂ)‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ W + z.im := by rw [abs_of_pos z.im_pos]; gcongr
    _ ≤ (W + 1) * (1 + z.im) ^ 1 := by
      nlinarith [mul_nonneg hW z.im_pos.le]

end StripGrowth

open MTT.Cohomology MvPolynomial

/-- Coefficient bounds survive any fixed linear map on a homogeneous binary space. -/
theorem stripGrowth_linear_coeff {W : ℝ} {n : ℕ} (P : ℍ → Binary ℂ)
    (hP : ∀ z, P z ∈ MTT.Cohomology.Sym ℂ n) (L : Binary ℂ →ₗ[ℂ] Binary ℂ)
    (hb : ∀ e, StripGrowth W (fun z => coeff e (P z))) (e : Fin 2 →₀ ℕ) :
    StripGrowth W (fun z => coeff e (L (P z))) := by
  classical
  have heq (z : ℍ) : coeff e (L (P z)) = ∑ j : Fin (n + 1),
      coeff ((homogeneousExponentEquiv n).symm j).val (P z) *
        coeff e (L (X 0 ^ j.val * X 1 ^ (n - j.val))) := by
    have hex := symmetricPower_expansion (⟨P z, hP z⟩ : MTT.Cohomology.Sym ℂ n)
    change P z = _ at hex
    conv_lhs => rw [hex]
    simp only [map_sum, coeff_sum, map_smul, coeff_smul, smul_eq_mul,
      symmetricPowerCoordinates_apply]
  simp_rw [heq]
  apply StripGrowth.sum
  intro j _
  exact (hb _).mul (StripGrowth.const _)

/-- The inverse chart action in the primitive's growth hypothesis can be removed. -/
theorem stripGrowth_coeff_of_inverse_action {W : ℝ} {n : ℕ}
    (P : ℍ → Binary ℂ) (hP : ∀ z, P z ∈ MTT.Cohomology.Sym ℂ n)
    (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hb : ∀ e, StripGrowth W (fun z => coeff e (act (σ⁻¹).val (P z))))
    (e : Fin 2 →₀ ℕ) : StripGrowth W (fun z => coeff e (P z)) := by
  have h := stripGrowth_linear_coeff (fun z => act (σ⁻¹).val (P z))
    (fun z => act_mem_sym _ (hP z)) (act σ.val) hb e
  simpa only [← act_matrix_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, act_one] using h

/-- Integral Möbius denominators have norm at least one above height one. -/
theorem one_le_norm_denom (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (z : ℍ) (hz : 1 ≤ z.im) : 1 ≤ ‖denom σ z‖ := by
  by_cases hc : σ 1 0 = 0
  · have hd := σ.property
    rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hd
    have hd1 : σ 1 1 = 1 ∨ σ 1 1 = -1 := by
      exact Int.eq_one_or_neg_one_of_mul_eq_one (by rwa [mul_comm])
    rcases hd1 with hd1 | hd1 <;> simp [denom, hc, hd1]
  · have hc1 : (1 : ℝ) ≤ |(σ 1 0 : ℝ)| := by
      exact_mod_cast (Int.one_le_abs hc)
    calc
      1 ≤ |(σ 1 0 : ℝ)| * z.im := one_le_mul_of_one_le_of_one_le hc1 hz
      _ = |(denom σ z).im| := by simp [denom, abs_mul, abs_of_pos z.im_pos]
      _ ≤ ‖denom σ z‖ := Complex.abs_im_le_norm _

/-- A Möbius denominator grows at most linearly on a bounded strip. -/
theorem stripGrowth_denom {W : ℝ} (hW : 0 ≤ W)
    (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    StripGrowth W (fun z => denom σ z) :=
  ((StripGrowth.const _).mul (StripGrowth.coe hW)).add (StripGrowth.const _)

/-- The inverse denominator is bounded above height one. -/
theorem stripGrowth_inv_denom (W : ℝ) (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    StripGrowth W (fun z => (denom σ z)⁻¹) := by
  refine ⟨1, 0, zero_le_one, fun z hz _ => ?_⟩
  simpa using inv_le_one_of_one_le₀ (one_le_norm_denom σ z hz)

/-- An integral Möbius transform has polynomial growth on a bounded strip. -/
theorem stripGrowth_smul {W : ℝ} (hW : 0 ≤ W)
    (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    StripGrowth W (fun z => ((σ • z : ℍ) : ℂ)) := by
  have hnum : StripGrowth W (fun z => num σ z) :=
    ((StripGrowth.const _).mul (StripGrowth.coe hW)).add (StripGrowth.const _)
  have heq (z : ℍ) : ((σ • z : ℍ) : ℂ) = num σ z * (denom σ z)⁻¹ := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [div_eq_mul_inv, num, denom]
  simpa only [heq] using
    hnum.mul (stripGrowth_inv_denom W σ)

end MTT.CuspDecay

end Part2

section Part3
/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

/-! # From exponential decay on cusp strips to uniform decay at infinity -/

set_option autoImplicit false
open UpperHalfPlane Complex Filter ModularForm
open scoped Topology MatrixGroups Modular ComplexConjugate Pointwise

namespace MTT.CuspDecay

/-- Uniform decay on a bounded vertical strip. -/
def StripDecay (W : ℝ) (f : ℍ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ H : ℝ, ∀ z : ℍ,
    H ≤ z.im → |z.re| ≤ W → ‖f z‖ ≤ ε

theorem StripDecay.conjugate {W : ℝ} {f : ℍ → ℂ} (hf : StripDecay W f) :
    StripDecay W (fun z => conj (f z)) := by
  simpa only [StripDecay, Complex.norm_conj] using hf

-- The shift argument is adapted from the verified AINTLIB UpperCuspBoundary port,
-- source commit eb9621e7bcb0ce220ad53983ec45d987cb5b9002 (Apache 2.0).
private theorem tendsto_one_add_pow_mul_exp (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun y : ℝ => (1 + y) ^ n * Real.exp (-c * y)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) c hc).comp
    (tendsto_atTop_add_const_left atTop 1 tendsto_id)
  simp only [Function.comp_def, Real.rpow_natCast] at h
  have heq (y : ℝ) : (1 + y) ^ n * Real.exp (-c * y) =
      Real.exp c * ((1 + y) ^ n * Real.exp (-c * (1 + y))) := by
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  simpa only [mul_zero, ← heq, id_eq] using h.const_mul (Real.exp c)

/-- Exponential cusp-form decay dominates any stripwise polynomial growth. -/
theorem cusp_mul_stripGrowth {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    {k : ℤ} {W : ℝ} (f : CuspForm Γ k) {P : ℍ → ℂ} (hP : StripGrowth W P) :
    StripDecay W (fun z => f z * P z) := by
  obtain ⟨D, n, hD, hP⟩ := hP
  obtain ⟨c, hc, hO⟩ := CuspFormClass.exp_decay_atImInfty' f
  obtain ⟨C, hC, hbound⟩ := hO.exists_pos
  rw [Asymptotics.IsBigOWith] at hbound
  rw [Filter.Eventually, atImInfty_mem] at hbound
  obtain ⟨B, hB⟩ := hbound
  have ht : Tendsto (fun y : ℝ => C * D * ((1 + y) ^ n * Real.exp (-c * y)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_one_add_pow_mul_exp n hc).const_mul (C * D)
  intro ε hε
  obtain ⟨H, hH⟩ := eventually_atTop.mp ((tendsto_order.mp ht).2 ε hε)
  refine ⟨max 1 (max B H), fun z hz hw => ?_⟩
  have hz1 : 1 ≤ z.im := (le_max_left _ _).trans hz
  have hzB : B ≤ z.im := (le_max_left B H).trans ((le_max_right _ _).trans hz)
  have hzH : H ≤ z.im := (le_max_right B H).trans ((le_max_right _ _).trans hz)
  have hf : ‖f z‖ ≤ C * Real.exp (-c * z.im) := by simpa using hB z hzB
  calc
    ‖f z * P z‖ ≤ (C * Real.exp (-c * z.im)) * (D * (1 + z.im) ^ n) := by
      rw [norm_mul]
      exact mul_le_mul hf (hP z hz1 hw) (norm_nonneg _) (by positivity)
    _ = C * D * ((1 + z.im) ^ n * Real.exp (-c * z.im)) := by ring
    _ ≤ ε := (hH z.im hzH).le

open ConjAct Pointwise Matrix.SpecialLinearGroup in
/-- Arithmeticity is preserved by an integral change of cusp chart. -/
theorem isArithmetic_chart {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (σ : SL(2, ℤ)) : (toConjAct (σ : GL (Fin 2) ℝ)⁻¹ • Γ).IsArithmetic := by
  simpa [(show Rat.castHom ℝ = algebraMap ℚ ℝ from rfl), map_inv, map_mapGL]
    using! Subgroup.IsArithmetic.conj Γ (mapGL ℚ σ)⁻¹

/-- Polynomial factors remain negligible in every integral cusp chart. -/
theorem cusp_smul_mul_stripGrowth {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    {k : ℕ} {W : ℝ} (hW : 0 ≤ W) (f : CuspForm Γ (k : ℤ))
    (σ : SL(2, ℤ)) {P : ℍ → ℂ} (hP : StripGrowth W P) :
    StripDecay W (fun z => f (σ • z) * P z) := by
  have := isArithmetic_chart (Γ := Γ) σ
  have h := cusp_mul_stripGrowth (CuspForm.translate f σ)
    (((stripGrowth_denom hW σ).pow k).mul hP)
  have heq (z : ℍ) : (CuspForm.translate f σ) z * (denom σ z ^ k * P z) =
      f (σ • z) * P z := by
    change (⇑f ∣[(k : ℤ)] σ) z * (denom σ z ^ k * P z) = _
    rw [ModularForm.SL_slash_apply, zpow_neg, zpow_natCast]
    field_simp [denom_ne_zero σ z]
  simpa only [heq] using h

/-- Positive real periodicity upgrades bounded-strip decay to full cusp decay. -/
theorem isZeroAtImInfty_of_periodic_stripDecay {W : ℝ} (hW : 0 < W)
    {f : ℍ → ℂ} (hper : Function.Periodic (f ∘ ofComplex) (W : ℂ))
    (hf : StripDecay W f) : IsZeroAtImInfty f := by
  rw [isZeroAtImInfty_iff]
  intro ε hε
  obtain ⟨H, hH⟩ := hf ε hε
  refine ⟨H, fun z hz => ?_⟩
  have hp : Function.Periodic (fun x : ℝ => f (ofComplex (x + Complex.I * z.im))) W := by
    intro x
    simpa only [Function.comp_apply, Complex.ofReal_add, add_right_comm] using
      hper ((x : ℂ) + Complex.I * z.im)
  obtain ⟨x, hx, heq⟩ := hp.exists_mem_Ico₀ hW z.re
  let w : ℍ := ⟨(x : ℂ) + Complex.I * z.im, by simpa using z.im_pos⟩
  have hw : w.im = z.im := by simp [w]
  have hwre : |w.re| ≤ W := by
    simpa [w, abs_of_nonneg hx.1] using hx.2.le
  have hfz : f z = f w := by
    have hzc : (z.re : ℂ) + Complex.I * z.im = (z : ℂ) := by
      simpa only [coe_re, coe_im, mul_comm] using Complex.re_add_im (z : ℂ)
    change f (ofComplex _) = f (ofComplex (w : ℂ)) at heq
    simpa only [hzc, ofComplex_apply] using heq
  rw [hfz]
  exact hH w (hw ▸ hz) hwre

/-- For an arithmetic level, stripwise cusp decay of an invariant antiholomorphic
one-form implies decay uniformly in every cusp chart. -/
theorem isZeroAtImInfty_pullback_of_equivariant {Γ : Subgroup SL(2, ℤ)}
    [(Γ.map (Matrix.SpecialLinearGroup.mapGL ℝ)).IsArithmetic]
    (A : ℂ → ℂ)
    (hA : ∀ γ ∈ Γ, ∀ z : ℍ,
      A ((γ • z : ℍ) : ℂ) = (starRingEnd ℂ (denom γ z)) ^ 2 * A z)
    (hdec : ∀ σ : SL(2, ℤ), ∀ W : ℝ, 0 < W → StripDecay W
      (fun z => A ((σ • z : ℍ) : ℂ) * ((starRingEnd ℂ (denom σ z)) ^ 2)⁻¹))
    (σ : SL(2, ℤ)) : IsZeroAtImInfty
      (fun z => A ((σ • z : ℍ) : ℂ) * ((starRingEnd ℂ (denom σ z)) ^ 2)⁻¹) := by
  let F : SlashInvariantForm (Γ.map (Matrix.SpecialLinearGroup.mapGL ℝ)) 2 :=
    { toFun := fun z => conj (A z)
      slash_action_eq' := by
        rintro _ ⟨γ, hγ, rfl⟩
        funext z
        change ((fun z : ℍ => conj (A z)) ∣[(2 : ℤ)] γ) z = _
        rw [ModularForm.SL_slash_apply, hA γ hγ z]
        simp only [map_mul, map_pow, starRingEnd_self_apply, zpow_neg, zpow_ofNat]
        field_simp [denom_ne_zero γ z] }
  have := isArithmetic_chart (Γ := Γ.map (Matrix.SpecialLinearGroup.mapGL ℝ)) σ
  let G := SlashInvariantForm.translate F σ
  let Δ := ConjAct.toConjAct (σ : GL (Fin 2) ℝ)⁻¹ •
    Γ.map (Matrix.SpecialLinearGroup.mapGL ℝ)
  let W := Δ.strictWidthInfty
  have hW : 0 < W := Δ.strictWidthInfty_pos
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex G
    Δ.strictWidthInfty_mem_strictPeriods
  have heq (z : ℍ) : conj (G z) =
      A ((σ • z : ℍ) : ℂ) * ((starRingEnd ℂ (denom σ z)) ^ 2)⁻¹ := by
    change conj (((fun z : ℍ => conj (A z)) ∣[(2 : ℤ)] σ) z) = _
    simp [ModularForm.SL_slash_apply, zpow_neg]
  apply isZeroAtImInfty_of_periodic_stripDecay hW
  · simpa only [Function.comp_def, heq] using hper.comp (starRingEnd ℂ)
  · exact hdec σ W hW

end MTT.CuspDecay

end Part3

section Part4
/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

/-! # Uniform cusp decay of mixed-period test functions -/

set_option autoImplicit false
open UpperHalfPlane Complex Filter MvPolynomial
open scoped Topology BigOperators MatrixGroups Modular ComplexConjugate

namespace MTT.CuspDecay
open MTT.Cohomology

/-- A finite coefficient contraction preserves polynomial strip growth. -/
theorem stripGrowth_contraction {W : ℝ} (n : ℕ) (P Q : ℍ → Binary ℂ)
    (hP : ∀ j, j ≤ n → StripGrowth W (fun z => coeff (binaryExponent n j) (P z)))
    (hQ : ∀ j, j ≤ n → StripGrowth W (fun z => coeff (binaryExponent n j) (Q z))) :
    StripGrowth W (fun z => periodContraction n (P z) (Q z)) := by
  unfold periodContraction
  apply StripGrowth.sum
  intro j hj
  simp only [div_eq_mul_inv]
  exact (((StripGrowth.const _).mul (hP j (by simpa using hj))).mul
    (hQ (n - j) (Nat.sub_le _ _))).mul (StripGrowth.const _)

/-- Every coefficient of a pure power has polynomial strip growth. -/
theorem stripGrowth_power_coeff {W : ℝ} {f : ℍ → ℂ} (hf : StripGrowth W f)
    (n j : ℕ) (hj : j ≤ n) :
    StripGrowth W (fun z => coeff (binaryExponent n j) (periodPower n (f z))) := by
  simpa only [MTT.PeriodMeasure.coeff_periodPower n j hj] using
    (StripGrowth.const (n.choose j : ℂ)).mul (hf.pow j)

/-- The mixed primitive has polynomial growth in every fixed chart. -/
theorem stripGrowth_primitive_coeff {N k : ℕ}
    {g v : CuspForm (MTT.GammaOne N) (k : ℤ)} {U : ℂ → Binary ℂ}
    (hU : IsMixedPeriodPrimitive g v U) (σ : SL(2, ℤ)) {W : ℝ} (hW : 0 < W)
    (e : Fin 2 →₀ ℕ) :
    StripGrowth W (fun z => coeff e (U (σ • z : ℍ))) := by
  apply stripGrowth_coeff_of_inverse_action (fun z => U (σ • z : ℍ))
    (fun z => hU.1 (σ • z)) σ
  intro e
  exact hU.2.2.2 σ e W hW

/-- The period contraction is linear in its right argument. -/
theorem contraction_smul_right (n : ℕ) (P Q : Binary ℂ) (a : ℂ) :
    periodContraction n P (a • Q) = a * periodContraction n P Q := by
  simpa only [one_smul, one_mul] using
    MTT.PeriodMeasure.periodContraction_smul_smul n 1 a P Q

/-- The period contraction is linear in its left argument. -/
theorem contraction_smul_left (n : ℕ) (P Q : Binary ℂ) (a : ℂ) :
    periodContraction n (a • P) Q = a * periodContraction n P Q := by
  simpa only [one_smul, mul_one] using
    MTT.PeriodMeasure.periodContraction_smul_smul n a 1 P Q

/-- Exponential cusp-form decay dominates the mixed primitive on each bounded strip. -/
theorem mixed_period_strip_decay {N k : ℕ} (hN : 0 < N)
    (g v q : CuspForm (MTT.GammaOne N) (k : ℤ))
    (U : ℂ → Binary ℂ) (hU : IsMixedPeriodPrimitive g v U)
    (σ : SL(2, ℤ)) {W : ℝ} (hW : 0 < W) :
    StripDecay W (fun z : ℍ =>
      periodContraction (k - 2) (U (σ • z : ℍ))
        (conj (q (σ • z)) • periodPower (k - 2) (conj ((σ • z : ℍ) : ℂ))) *
        ((starRingEnd ℂ (denom σ z)) ^ 2)⁻¹) ∧
    StripDecay W (fun z : ℍ => conj (
      periodContraction (k - 2)
        (q (σ • z) • periodPower (k - 2) ((σ • z : ℍ) : ℂ)) (U (σ • z : ℍ))) *
        ((starRingEnd ℂ (denom σ z)) ^ 2)⁻¹) := by
  let : NeZero N := ⟨hN.ne'⟩
  let : (MTT.GammaOne N).IsArithmetic := by dsimp [MTT.GammaOne]; infer_instance
  have hcoeff := stripGrowth_primitive_coeff hU σ hW
  have hmob := stripGrowth_smul hW.le σ
  have hi := (stripGrowth_inv_denom W σ).pow 2
  have h1 := stripGrowth_contraction (k - 2) (fun z => U (σ • z : ℍ))
    (fun z => periodPower (k - 2) (conj ((σ • z : ℍ) : ℂ)))
    (fun j _ => hcoeff _) (fun j hj => stripGrowth_power_coeff hmob.conjugate _ j hj)
  have h2 := stripGrowth_contraction (k - 2)
    (fun z => periodPower (k - 2) ((σ • z : ℍ) : ℂ)) (fun z => U (σ • z : ℍ))
    (fun j hj => stripGrowth_power_coeff hmob _ j hj) (fun j _ => hcoeff _)
  constructor
  · have hd := (cusp_smul_mul_stripGrowth hW.le q σ
      (h1.conjugate.mul hi)).conjugate
    simpa only [contraction_smul_right, map_mul, starRingEnd_self_apply,
      map_pow, map_inv₀, inv_pow, mul_assoc] using hd
  · have hd := (cusp_smul_mul_stripGrowth hW.le q σ (h2.mul hi)).conjugate
    simpa only [contraction_smul_left, map_mul, map_pow, map_inv₀, inv_pow,
      mul_assoc] using hd

end MTT.CuspDecay

namespace MTT.Cohomology

/-- The two mixed-period one-forms vanish uniformly in every cusp chart. -/
theorem mixed_period_test_functions_cusp_decay_of_pos_level_aux
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (g v q : CuspForm (MTT.GammaOne N) (k : ℤ))
    (U : ℂ → Binary ℂ) (hU : IsMixedPeriodPrimitive g v U) :
    let A₁ : ℂ → ℂ := fun z =>
      periodContraction (k - 2) (U z)
        (conj ((↑ₕ(fun τ : ℍ ↦ q τ)) z) • periodPower (k - 2) (conj z))
    let A₂ : ℂ → ℂ := fun z => conj <|
      periodContraction (k - 2)
        (((↑ₕ(fun τ : ℍ ↦ q τ)) z) • periodPower (k - 2) z) (U z)
    (∀ σ : Matrix.SpecialLinearGroup (Fin 2) ℤ, IsZeroAtImInfty
      fun τ : ℍ ↦ A₁ ((σ • τ : ℍ) : ℂ) *
        ((starRingEnd ℂ (denom σ τ)) ^ 2)⁻¹) ∧
    (∀ σ : Matrix.SpecialLinearGroup (Fin 2) ℤ, IsZeroAtImInfty
      fun τ : ℍ ↦ A₂ ((σ • τ : ℍ) : ℂ) *
        ((starRingEnd ℂ (denom σ τ)) ^ 2)⁻¹) := by
  let : NeZero N := ⟨hN.ne'⟩
  let : (MTT.GammaOne N).IsArithmetic := by dsimp [MTT.GammaOne]; infer_instance
  let A₁ : ℂ → ℂ := fun z => periodContraction (k - 2) (U z)
    (conj ((↑ₕ(fun τ : ℍ ↦ q τ)) z) • periodPower (k - 2) (conj z))
  let A₂ : ℂ → ℂ := fun z => conj <| periodContraction (k - 2)
    (((↑ₕ(fun τ : ℍ ↦ q τ)) z) • periodPower (k - 2) z) (U z)
  change (∀ σ : SL(2, ℤ), IsZeroAtImInfty (fun τ : ℍ =>
    A₁ ((σ • τ : ℍ) : ℂ) * ((starRingEnd ℂ (denom σ τ)) ^ 2)⁻¹)) ∧
    (∀ σ : SL(2, ℤ), IsZeroAtImInfty (fun τ : ℍ =>
    A₂ ((σ • τ : ℍ) : ℂ) * ((starRingEnd ℂ (denom σ τ)) ^ 2)⁻¹))
  have hlocal := mixed_period_test_functions_local_equivariant hk g v q U hU
  constructor
  · intro σ
    refine MTT.CuspDecay.isZeroAtImInfty_pullback_of_equivariant
      (Γ := CongruenceSubgroup.Gamma1 N) A₁ hlocal.2.1 ?_ σ
    intro δ W hW
    simpa [A₁] using (MTT.CuspDecay.mixed_period_strip_decay hN g v q U hU δ hW).1
  · intro σ
    refine MTT.CuspDecay.isZeroAtImInfty_pullback_of_equivariant
      (Γ := CongruenceSubgroup.Gamma1 N) A₂ hlocal.2.2.2.2.1 ?_ σ
    intro δ W hW
    simpa [A₂] using (MTT.CuspDecay.mixed_period_strip_decay hN g v q U hU δ hW).2

end MTT.Cohomology

end Part4

open UpperHalfPlane MeasureTheory MTT.Cohomology
open scoped MatrixGroups Modular ComplexConjugate

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (g v q : CuspForm (MTT.GammaOne N) (k : ℤ))
    (U : ℂ → Binary ℂ) (hU : IsMixedPeriodPrimitive g v U) :
    let A₁ : ℂ → ℂ := fun z =>
      periodContraction (k - 2) (U z)
        (conj ((↑ₕ(fun τ : ℍ ↦ q τ)) z) • periodPower (k - 2) (conj z))
    let A₂ : ℂ → ℂ := fun z => conj <|
      periodContraction (k - 2)
        (((↑ₕ(fun τ : ℍ ↦ q τ)) z) • periodPower (k - 2) z) (U z)
    (∀ σ : Matrix.SpecialLinearGroup (Fin 2) ℤ, IsZeroAtImInfty
      fun τ : ℍ ↦ A₁ ((σ • τ : ℍ) : ℂ) *
        ((starRingEnd ℂ (denom σ τ)) ^ 2)⁻¹) ∧
    (∀ σ : Matrix.SpecialLinearGroup (Fin 2) ℤ, IsZeroAtImInfty
      fun τ : ℍ ↦ A₂ ((σ • τ : ℍ) : ℂ) *
        ((starRingEnd ℂ (denom σ τ)) ^ 2)⁻¹) :=
  MTT.Cohomology.mixed_period_test_functions_cusp_decay_of_pos_level_aux hN hk g v q U hU
