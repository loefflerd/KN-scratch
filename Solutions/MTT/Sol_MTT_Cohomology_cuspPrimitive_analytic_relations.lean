import Theorems.MTT.Thm_MTT_Cohomology_cuspPrimitive_slash_relation
import Definitions.MTT.Def_MTT_Cohomology_Integration
import Mathlib.RingTheory.Flat.Basic
import Mathlib.NumberTheory.ModularForms.LFunction
import Mathlib.NumberTheory.ModularForms.Identities
set_option autoImplicit false
noncomputable section
open scoped BigOperators ModularForm TensorProduct MatrixGroups Pointwise
open MeasureTheory Complex UpperHalfPlane Matrix CongruenceSubgroup
open MTT MTT.Cohomology ModularForm
open ConjAct

namespace MTT.HeckePort

/-! ### Integer matrices as elements of `GL₂(ℚ)` and `GL₂(ℝ)` -/

/-- An integer matrix viewed in `GL₂(ℚ)` (junk value `1` if the determinant vanishes). -/
def toGLQ (A : Matrix (Fin 2) (Fin 2) ℤ) : GL (Fin 2) ℚ :=
  if h : ((Int.castRingHom ℚ).mapMatrix A).det ≠ 0 then
    Matrix.GeneralLinearGroup.mkOfDetNeZero _ h else 1

/-- An integer matrix viewed in `GL₂(ℝ)`, through `GL₂(ℚ)`. -/
def toGL (A : Matrix (Fin 2) (Fin 2) ℤ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (toGLQ A)

lemma det_map_ne_zero {A : Matrix (Fin 2) (Fin 2) ℤ} (h : A.det ≠ 0) :
    ((Int.castRingHom ℚ).mapMatrix A).det ≠ 0 := by
  rw [← RingHom.map_det]; simpa using h

lemma toGLQ_val {A : Matrix (Fin 2) (Fin 2) ℤ} (h : A.det ≠ 0) :
    (toGLQ A : Matrix (Fin 2) (Fin 2) ℚ) = (Int.castRingHom ℚ).mapMatrix A := by
  rw [toGLQ, dite_eq_left (det_map_ne_zero h)]; rfl

lemma toGL_apply {A : Matrix (Fin 2) (Fin 2) ℤ} (h : A.det ≠ 0) (i j : Fin 2) :
    (toGL A : Matrix (Fin 2) (Fin 2) ℝ) i j = (A i j : ℝ) := by
  rw [toGL, Matrix.GeneralLinearGroup.map_apply, toGLQ_val h]
  simp

lemma toGL_det_matrix {A : Matrix (Fin 2) (Fin 2) ℤ} (h : A.det ≠ 0) :
    (toGL A : Matrix (Fin 2) (Fin 2) ℝ).det = (A.det : ℝ) := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [toGL_apply h]
  push_cast; ring

lemma toGL_det {A : Matrix (Fin 2) (Fin 2) ℤ} (h : A.det ≠ 0) :
    (Matrix.GeneralLinearGroup.det (toGL A) : ℝ) = (A.det : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, toGL_det_matrix h]

lemma toGL_mul {A B : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    toGL (A * B) = toGL A * toGL B := by
  have hAB : (A * B).det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero hA hB
  ext i j
  rw [Units.val_mul, Matrix.mul_apply, toGL_apply hAB, Matrix.mul_apply]
  simp only [toGL_apply hA, toGL_apply hB]
  push_cast; rfl

lemma toGL_SL (γ : SL(2, ℤ)) :
    toGL (γ : Matrix (Fin 2) (Fin 2) ℤ) = Matrix.SpecialLinearGroup.mapGL ℝ γ := by
  ext i j
  rw [toGL_apply (by simp), Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  simp

lemma toGL_det_pos {A : Matrix (Fin 2) (Fin 2) ℤ} (h : 0 < A.det) :
    0 < (Matrix.GeneralLinearGroup.det (toGL A) : ℝ) := by
  rw [toGL_det h.ne']; exact_mod_cast h

lemma σ_toGL {A : Matrix (Fin 2) (Fin 2) ℤ} (h : 0 < A.det) (z : ℂ) : σ (toGL A) z = z := by
  simp [σ, toGL_det_matrix h.ne', h]

lemma coe_toGL_smul {A : Matrix (Fin 2) (Fin 2) ℤ} (h : 0 < A.det) (τ : ℍ) :
    ((toGL A • τ : ℍ) : ℂ) =
      ((A 0 0 : ℂ) * τ + (A 0 1 : ℂ)) / ((A 1 0 : ℂ) * τ + (A 1 1 : ℂ)) := by
  rw [coe_smul_of_det_pos (toGL_det_pos h)]
  simp [num, denom, toGL_apply h.ne']

lemma slash_toGL_apply {A : Matrix (Fin 2) (Fin 2) ℤ} (h : 0 < A.det) (k : ℤ) (f : ℍ → ℂ)
    (τ : ℍ) :
    (f ∣[k] toGL A) τ =
      f (toGL A • τ) * (A.det : ℂ) ^ (k - 1) * ((A 1 0 : ℂ) * τ + (A 1 1 : ℂ)) ^ (-k) := by
  rw [ModularForm.slash_apply, σ_toGL h, toGL_det h.ne', abs_of_pos (by exact_mod_cast h)]
  simp [denom, toGL_apply h.ne']

lemma slash_mapGL_apply (γ : SL(2, ℤ)) (k : ℤ) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ γ) τ =
      f (Matrix.SpecialLinearGroup.mapGL ℝ γ • τ) *
        (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ (-k) := by
  rw [← toGL_SL, slash_toGL_apply (by simp)]
  simp

lemma denom_SL_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) :
    ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
  have := denom_ne_zero (toGL (γ : Matrix (Fin 2) (Fin 2) ℤ)) τ
  simpa [denom, toGL_apply (show (γ : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 by simp)] using this


end MTT.HeckePort

namespace MTT.AnalyticRelations
open MTT.HeckePort

lemma rational_translate_integrable
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (f : CuspForm (GammaOne N) (k : ℤ)) (r : ℚ) (j : ℕ) :
    IntegrableOn (fun t : ℝ =>
      f (ofComplex ((r : ℂ) + Complex.I * t)) * (t : ℂ)^j) (Set.Ioi 0) := by
  let : NeZero N := ⟨by omega⟩
  let g : GL (Fin 2) ℚ := Matrix.GeneralLinearGroup.upperRightHom r
  let gr : GL (Fin 2) ℝ := g.map (Rat.castHom ℝ)
  have hr : gr = Matrix.GeneralLinearGroup.upperRightHom (r : ℝ) := by
    ext i l
    fin_cases i <;> fin_cases l <;> simp [gr, g]
  let : (GammaOne N).IsArithmetic := by dsimp [GammaOne]; infer_instance
  let : (toConjAct gr⁻¹ • GammaOne N).IsArithmetic := by
    have hh := Subgroup.IsArithmetic.conj (GammaOne N) g⁻¹
    simpa [gr] using hh
  let F := CuspForm.translate f gr
  have hconv := ((CuspForm.isStrongFEPair (by omega : (0 : ℤ) < k) F).hasMellin
    ((j : ℂ)+1)).1
  unfold MellinConvergent at hconv
  have hval (t : ℝ) (ht : 0 < t) :
      F (ofComplex (Complex.I * t)) = f (ofComplex ((r : ℂ) + Complex.I * t)) := by
    change (⇑f ∣[(k : ℤ)] gr) _ = _
    rw [slash_def, hr]
    simp only [Matrix.GeneralLinearGroup.val_det_apply]
    simp [σ, denom, Matrix.GeneralLinearGroup.upperRightHom]
    congr 1
    ext
    simp [coe_smul, σ, num, denom, ofComplex_apply_of_im_pos, ht]
    ring
  apply hconv.congr_fun _ measurableSet_Ioi
  intro t ht
  simp only [ModularForm.weakFEPair, add_sub_cancel_right, Complex.cpow_natCast,
    smul_eq_mul, hval t ht]
  ring


/-- The integrand `t ↦ F(r+it) P(r+it)` of the modular integral. -/
def vint (F : ℍ → ℂ) (P : Polynomial ℂ) (r : ℚ) (t : ℝ) : ℂ :=
  F (ofComplex ((r : ℂ) + Complex.I * t)) * P.eval ((r : ℂ) + Complex.I * t)

lemma modularIntegral_eq (F : ℍ → ℂ) (P : Polynomial ℂ) (r : ℚ) :
    modularIntegral F P r = (2 * Real.pi : ℂ) * ∫ t in Set.Ioi (0 : ℝ), vint F P r t := rfl

/-- Integrability of `t ↦ F(r+it) t^j` on `(0,∞)` for all `j`. -/
def GoodAt (F : ℍ → ℂ) (r : ℚ) : Prop :=
  ∀ j : ℕ, IntegrableOn (fun t : ℝ => F (ofComplex ((r : ℂ) + Complex.I * t)) * (t : ℂ) ^ j)
    (Set.Ioi 0)

lemma goodAt_of_cuspForm {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (f : CuspForm (GammaOne N) (k : ℤ)) (r : ℚ) : GoodAt f r :=
  fun j => rational_translate_integrable hN hk f r j

lemma GoodAt.pow {F : ℍ → ℂ} {r : ℚ} (h : GoodAt F r) (n : ℕ) :
    IntegrableOn (fun t : ℝ => F (ofComplex ((r : ℂ) + Complex.I * t)) *
      ((r : ℂ) + Complex.I * t) ^ n) (Set.Ioi 0) := by
  have : (fun t : ℝ => F (ofComplex ((r : ℂ) + Complex.I * t)) * ((r : ℂ) + Complex.I * t) ^ n) =
      fun t : ℝ => ∑ m ∈ Finset.range (n + 1),
        ((r : ℂ) ^ m * Complex.I ^ (n - m) * (n.choose m : ℂ)) *
          (F (ofComplex ((r : ℂ) + Complex.I * t)) * (t : ℂ) ^ (n - m)) := by
    funext t
    rw [add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_pow]; ring
  rw [this]
  exact integrable_finsetSum _ fun m _ => (h (n - m)).const_mul _

lemma GoodAt.integrable_vint {F : ℍ → ℂ} {r : ℚ} (h : GoodAt F r) (P : Polynomial ℂ) :
    IntegrableOn (vint F P r) (Set.Ioi 0) := by
  have : vint F P r = fun t : ℝ => ∑ i ∈ Finset.range (P.natDegree + 1),
      P.coeff i * (F (ofComplex ((r : ℂ) + Complex.I * t)) * ((r : ℂ) + Complex.I * t) ^ i) := by
    funext t
    simp only [vint, Polynomial.eval_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [this]
  exact integrable_finsetSum _ fun i _ => (h.pow i).const_mul _


lemma modularIntegral_add_form {F G : ℍ → ℂ} {r : ℚ} (hF : GoodAt F r) (hG : GoodAt G r)
    (P : Polynomial ℂ) :
    modularIntegral (F + G) P r = modularIntegral F P r + modularIntegral G P r := by
  simp only [modularIntegral_eq]
  rw [← mul_add, ← integral_add (hF.integrable_vint P) (hG.integrable_vint P)]
  congr 1
  refine setIntegral_congr_fun (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi fun t _ => ?_
  simp only [vint, Pi.add_apply]; ring

lemma modularIntegral_smul_form (F : ℍ → ℂ) (a : ℂ) (r : ℚ) (P : Polynomial ℂ) :
    modularIntegral (a • F) P r = a * modularIntegral F P r := by
  simp only [modularIntegral_eq]
  have : ∫ t in Set.Ioi (0 : ℝ), vint (a • F) P r t = a * ∫ t in Set.Ioi (0 : ℝ), vint F P r t := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi fun t _ => ?_
    simp only [vint, Pi.smul_apply, smul_eq_mul]; ring
  rw [this]; ring

/-- Pointwise `Γ₁(N)`-invariance. -/
lemma law_of_gamma1 {N k : ℕ} (f : CuspForm (GammaOne N) (k : ℤ)) (γ : Gamma1 N) (z : ℍ) :
    f (Matrix.SpecialLinearGroup.mapGL ℝ γ.val • z) =
      (((γ.val 1 0 : ℤ) : ℂ) * z + ((γ.val 1 1 : ℤ) : ℂ)) ^ k * f z := by
  have h := SlashInvariantFormClass.slash_action_eq f (Matrix.SpecialLinearGroup.mapGL ℝ γ.val)
    (Subgroup.mem_map.mpr ⟨γ.val, γ.2, rfl⟩)
  have hz := congrFun h z
  rw [slash_mapGL_apply, zpow_neg, zpow_natCast] at hz
  have hd := denom_SL_ne_zero γ.val z
  calc f (Matrix.SpecialLinearGroup.mapGL ℝ γ.val • z)
      = f (Matrix.SpecialLinearGroup.mapGL ℝ γ.val • z) *
          ((((γ.val 1 0 : ℤ) : ℂ) * z + ((γ.val 1 1 : ℤ) : ℂ)) ^ k)⁻¹ *
          (((γ.val 1 0 : ℤ) : ℂ) * z + ((γ.val 1 1 : ℤ) : ℂ)) ^ k := by field_simp
    _ = _ := by rw [hz]; ring

end MTT.AnalyticRelations

open MTT.AnalyticRelations in
theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) :
    (∀ (f : CuspForm (MTT.GammaOne N) (k : ℤ))
        (γ : CongruenceSubgroup.Gamma1 N) (x : Cusp),
      cuspPrimitive f (cuspAct γ.val x) =
        act γ.val.val (cuspPrimitive f x) +
          cuspPrimitive f (cuspAct γ.val OnePoint.infty)) ∧
    (∀ (f g : CuspForm (MTT.GammaOne N) (k : ℤ)) (x : Cusp),
      cuspPrimitive (f + g) x = cuspPrimitive f x + cuspPrimitive g x) ∧
    (∀ (a : ℂ) (f : CuspForm (MTT.GammaOne N) (k : ℤ)) (x : Cusp),
      cuspPrimitive (a • f) x = a • cuspPrimitive f x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro f γ x
    exact MTT.Cohomology.cuspPrimitive_slash_relation hN hk f f
      ⟨γ.val, CongruenceSubgroup.Gamma1_in_Gamma0 N γ.2⟩ (fun z => law_of_gamma1 f γ z) x
  · intro f g x
    rcases x with _ | r
    · simp [cuspPrimitive]
    · change cuspPeriodPolynomial (f + g) r = cuspPeriodPolynomial f r + cuspPeriodPolynomial g r
      unfold cuspPeriodPolynomial
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← map_add]
      congr 1
      rw [FunLike.coe_add, modularIntegral_add_form (goodAt_of_cuspForm hN hk f r)
        (goodAt_of_cuspForm hN hk g r)]
      ring
  · intro a f x
    rcases x with _ | r
    · simp [cuspPrimitive]
    · change cuspPeriodPolynomial (a • f) r = a • cuspPeriodPolynomial f r
      unfold cuspPeriodPolynomial
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [MvPolynomial.smul_monomial]
      congr 1
      rw [FunLike.coe_smul, modularIntegral_smul_form, smul_eq_mul]
      ring
