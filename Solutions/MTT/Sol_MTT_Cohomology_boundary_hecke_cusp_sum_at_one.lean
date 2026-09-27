import Definitions.MTT.Def_MTT_Cohomology_Boundary
import Definitions.MTT.Def_MTT_Cohomology_Integration
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Data.Nat.Prime.Int
import Mathlib.NumberTheory.LSeries.PrimesInAP
set_option autoImplicit false
noncomputable section
open scoped BigOperators MatrixGroups
open Matrix CongruenceSubgroup

namespace MTT.Cohomology

/-! ### Part 0: integer matrices, `fractional` as the `GL₂(ℚ)`-action -/



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
  rw [toGLQ, dif_pos (det_map_ne_zero h)]; rfl

lemma toGL_apply {A : Matrix (Fin 2) (Fin 2) ℤ} (h : A.det ≠ 0) (i j : Fin 2) :
    (toGL A : Matrix (Fin 2) (Fin 2) ℝ) i j = (A i j : ℝ) := by
  rw [toGL, Matrix.GeneralLinearGroup.map_apply, toGLQ_val h]
  simp


lemma toGLQ_apply {A : Matrix (Fin 2) (Fin 2) ℤ} (h : A.det ≠ 0) (i j : Fin 2) :
    (toGLQ A : Matrix (Fin 2) (Fin 2) ℚ) i j = (A i j : ℚ) := by
  rw [toGLQ_val h]; simp

lemma toGLQ_mul {A B : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    toGLQ (A * B) = toGLQ A * toGLQ B := by
  have hAB : (A * B).det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero hA hB
  ext i j
  rw [Units.val_mul, Matrix.mul_apply, toGLQ_apply hAB, Matrix.mul_apply]
  simp only [toGLQ_apply hA, toGLQ_apply hB]
  push_cast; rfl

lemma toGLQ_SL (γ : SL(2, ℤ)) :
    toGLQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = Matrix.SpecialLinearGroup.mapGL ℚ γ := by
  ext i j
  rw [toGLQ_apply (by simp), Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  simp

/-- The platform's `fractional` is the action of `GL₂(ℚ)` on `P¹(ℚ)`. -/
lemma fractional_eq_smul {A : Matrix (Fin 2) (Fin 2) ℤ} (h : A.det ≠ 0) (x : Cusp) :
    fractional A x = toGLQ A • x := by
  rcases x with _ | r
  · change fractional A OnePoint.infty = toGLQ A • (OnePoint.infty : OnePoint ℚ)
    rw [OnePoint.smul_infty_eq_ite]
    simp only [fractional, toGLQ_apply h]
    by_cases hc : A 1 0 = 0
    · simp [hc]
    · have hc' : (A 1 0 : ℚ) ≠ 0 := by exact_mod_cast hc
      simp [hc, hc']
  · change fractional A (r : OnePoint ℚ) = toGLQ A • (r : OnePoint ℚ)
    rw [OnePoint.smul_some_eq_ite]
    simp only [fractional, toGLQ_apply h]

lemma fractional_mul {A B : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det ≠ 0) (hB : B.det ≠ 0) (x : Cusp) :
    fractional (A * B) x = fractional A (fractional B x) := by
  have hAB : (A * B).det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero hA hB
  rw [fractional_eq_smul hAB, fractional_eq_smul hA, fractional_eq_smul hB, toGLQ_mul hA hB,
    mul_smul]

lemma fractional_SL (γ : SL(2, ℤ)) (x : Cusp) :
    fractional (γ : Matrix (Fin 2) (Fin 2) ℤ) x = cuspAct γ x := by
  rw [fractional_eq_smul (by simp), toGLQ_SL]; rfl

lemma binaryExponent_apply_zero (n j : ℕ) : binaryExponent n j 0 = j := by
  simp [binaryExponent]

lemma coeff_cuspPeriodPolynomial {N k : ℕ} (hk : 2 ≤ k) (f : CuspForm (MTT.GammaOne N) (k : ℤ))
    (r : ℚ) {j : ℕ} (hj : j ≤ k - 2) :
    MvPolynomial.coeff (binaryExponent (k - 2) j) (cuspPeriodPolynomial f r) =
      ((k - 2).choose j : ℂ) * MTT.modularIntegral f (Polynomial.X ^ j) r := by
  rw [cuspPeriodPolynomial, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [if_neg]
    intro h
    exact hij (by simpa [binaryExponent_apply_zero] using congrArg (fun v => v 0) h)
  · intro hj'
    exact absurd (Finset.mem_range.mpr (by omega)) hj'

lemma cuspPeriodPolynomial_mem_Sym {N k : ℕ} (hk : 2 ≤ k) (f : CuspForm (MTT.GammaOne N) (k : ℤ))
    (r : ℚ) : cuspPeriodPolynomial f r ∈ Sym ℂ (k - 2) := by
  unfold cuspPeriodPolynomial
  refine Submodule.sum_mem _ fun j hj => ?_
  rw [MvPolynomial.mem_homogeneousSubmodule]
  apply MvPolynomial.isHomogeneous_monomial
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  have := Finset.mem_range.mp hj
  simp [binaryExponent]
  omega

/-- Two homogeneous polynomials of degree `n` with the same `X^j Y^(n-j)`-coefficients agree. -/
lemma Sym_ext {n : ℕ} {P Q : Binary ℂ} (hP : P ∈ Sym ℂ n) (hQ : Q ∈ Sym ℂ n)
    (h : ∀ j ≤ n, MvPolynomial.coeff (binaryExponent n j) P =
      MvPolynomial.coeff (binaryExponent n j) Q) : P = Q := by
  rw [MvPolynomial.mem_homogeneousSubmodule] at hP hQ
  ext m
  by_cases hm : MvPolynomial.coeff m P = 0 ∧ MvPolynomial.coeff m Q = 0
  · rw [hm.1, hm.2]
  · have hdeg : m.degree = n := by
      rw [Finsupp.degree_eq_weight_one]
      rcases not_and_or.mp hm with h1 | h1
      · exact hP h1
      · exact hQ h1
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdeg
    have hm' : m = binaryExponent n (m 0) := by
      ext i
      fin_cases i <;> simp [binaryExponent]
      omega
    rw [hm']
    exact h (m 0) (by omega)

/-- The substitution underlying `act`, with its target algebra made explicit. -/
def actAlg (γ : Matrix (Fin 2) (Fin 2) ℤ) : Binary ℂ →ₐ[ℂ] Binary ℂ :=
  @MvPolynomial.aeval ℂ (Binary ℂ) (Fin 2) _ _ _
    (fun i : Fin 2 => ∑ a : Fin 2, ((γ a i : ℤ) : ℂ) • (MvPolynomial.X a : Binary ℂ))

lemma act_eq_actAlg (γ : Matrix (Fin 2) (Fin 2) ℤ) (P : Binary ℂ) : act γ P = actAlg γ P := rfl

lemma actAlg_comp (A B : Matrix (Fin 2) (Fin 2) ℤ) :
    (actAlg A).comp (actAlg B) = actAlg (A * B) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, actAlg, MvPolynomial.aeval_X, map_sum, map_smul,
    Matrix.mul_apply, Int.cast_sum, Int.cast_mul, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm]

lemma act_act (A B : Matrix (Fin 2) (Fin 2) ℤ) (P : Binary ℂ) :
    act A (act B P) = act (A * B) P := by
  rw [act_eq_actAlg, act_eq_actAlg, act_eq_actAlg, ← AlgHom.comp_apply, actAlg_comp]

lemma act_one (P : Binary ℂ) : act (1 : Matrix (Fin 2) (Fin 2) ℤ) P = P := by
  rw [act_eq_actAlg]
  have : actAlg 1 = AlgHom.id ℂ (Binary ℂ) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [actAlg, Matrix.one_apply]
  rw [this]
  rfl

lemma act_injective_of_det_one {γ : Matrix (Fin 2) (Fin 2) ℤ} (hγ : γ.det = 1) :
    Function.Injective (act γ : Binary ℂ → Binary ℂ) := by
  intro P Q h
  have := congrArg (act (Matrix.adjugate γ)) h
  rwa [act_act, act_act, Matrix.adjugate_mul, hγ, one_smul, act_one, act_one] at this

lemma binaryExponent_apply_one (n j : ℕ) : binaryExponent n j 1 = n - j := by
  simp [binaryExponent]

/-- A homogeneous polynomial of degree `n` is the sum of its `X^j Y^(n-j)` parts. -/
lemma Sym_as_sum {n : ℕ} {P : Binary ℂ} (hP : P ∈ Sym ℂ n) :
    P = ∑ j ∈ Finset.range (n + 1),
      MvPolynomial.monomial (binaryExponent n j) (MvPolynomial.coeff (binaryExponent n j) P) := by
  apply Sym_ext hP
  · refine Submodule.sum_mem _ fun j hj => ?_
    rw [MvPolynomial.mem_homogeneousSubmodule]
    apply MvPolynomial.isHomogeneous_monomial
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
    have := Finset.mem_range.mp hj
    simp [binaryExponent]
    omega
  · intro j hj
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      rw [if_neg]
      intro h
      exact hij (by simpa [binaryExponent_apply_zero] using congrArg (fun v => v 0) h)
    · intro hj'
      exact absurd (Finset.mem_range.mpr (by omega)) hj'

lemma actAlg_C (γ : Matrix (Fin 2) (Fin 2) ℤ) (c : ℂ) :
    actAlg γ (MvPolynomial.C c) = MvPolynomial.C c := by
  rw [actAlg, MvPolynomial.aeval_C]; rfl

lemma monomial_binaryExponent (n j : ℕ) (c : ℂ) :
    (MvPolynomial.monomial (binaryExponent n j) c : Binary ℂ) =
      MvPolynomial.C c * MvPolynomial.X 0 ^ j * MvPolynomial.X 1 ^ (n - j) := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two,
    binaryExponent_apply_zero, binaryExponent_apply_one, mul_assoc]

lemma fractional_refl_infty : fractional !![-1, 0; 0, 1] OnePoint.infty = OnePoint.infty := by
  (simp [fractional, OnePoint.infty]; rfl)

lemma fractional_refl_coe (r : ℚ) : fractional !![-1, 0; 0, 1] (r : Cusp) = ((-r : ℚ) : Cusp) := by
  change fractional !![-1, 0; 0, 1] (some r) = some (-r)
  simp [fractional]
  rfl

lemma reflection_add {R : Type*} [CommRing R] (φ ψ : (Cusp × Cusp) → Binary R) :
    reflection (φ + ψ) = reflection φ + reflection ψ := by
  funext D; simp [reflection]

lemma reflection_smul {R : Type*} [CommRing R] (c : R) (φ : (Cusp × Cusp) → Binary R) :
    reflection (c • φ) = c • reflection φ := by
  funext D; simp [reflection]


/-! ### `act` preserves homogeneity -/

lemma actAlg_X_isHomogeneous (γ : Matrix (Fin 2) (Fin 2) ℤ) (i : Fin 2) :
    MvPolynomial.IsHomogeneous (actAlg γ (MvPolynomial.X i)) 1 := by
  rw [actAlg, MvPolynomial.aeval_X]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun a _ => ?_
  rw [MvPolynomial.smul_eq_C_mul]
  simpa using (MvPolynomial.isHomogeneous_C (Fin 2) ((γ a i : ℤ) : ℂ)).mul
    (MvPolynomial.isHomogeneous_X ℂ a)

lemma act_mem_Sym {n : ℕ} (γ : Matrix (Fin 2) (Fin 2) ℤ) {P : Binary ℂ} (hP : P ∈ Sym ℂ n) :
    act γ P ∈ Sym ℂ n := by
  rw [Sym_as_sum hP, map_sum]
  refine Submodule.sum_mem _ fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  rw [monomial_binaryExponent, act_eq_actAlg, map_mul, map_mul, map_pow, map_pow, actAlg_C,
    MvPolynomial.mem_homogeneousSubmodule]
  have := ((MvPolynomial.isHomogeneous_C (Fin 2) (MvPolynomial.coeff (binaryExponent n j) P)).mul
    ((actAlg_X_isHomogeneous γ 0).pow j)).mul ((actAlg_X_isHomogeneous γ 1).pow (n - j))
  have e : 0 + 1 * j + 1 * (n - j) = n := by omega
  rw [e] at this
  exact this



/-! ### Part A: cusps as primitive vectors -/

/-- The canonical primitive vector of a cusp. -/
def vecOf : Cusp → (Fin 2 → ℤ)
  | none => ![1, 0]
  | some r => ![r.num, (r.den : ℤ)]

/-- The cusp of an integer vector. -/
def cuspOf (v : Fin 2 → ℤ) : Cusp :=
  if v 1 = 0 then OnePoint.infty else ((((v 0 : ℚ) / (v 1 : ℚ)) : ℚ) : Cusp)

lemma vecOf_infty : vecOf OnePoint.infty = ![1, 0] := rfl
lemma vecOf_coe (r : ℚ) : vecOf (r : Cusp) = ![r.num, (r.den : ℤ)] := rfl

lemma vecOf_isCoprime (x : Cusp) : IsCoprime (vecOf x 0) (vecOf x 1) := by
  rcases x with _ | r
  · exact isCoprime_one_left
  · change IsCoprime r.num (r.den : ℤ)
    exact Int.isCoprime_iff_gcd_eq_one.mpr r.reduced

lemma cuspOf_vecOf (x : Cusp) : cuspOf (vecOf x) = x := by
  rcases x with _ | r
  · rfl
  · have hd : (r.den : ℤ) ≠ 0 := by exact_mod_cast r.den_ne_zero
    show cuspOf ![r.num, (r.den : ℤ)] = ((r : ℚ) : Cusp)
    unfold cuspOf
    split_ifs with h
    · simp at h
    · congr 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast
      exact Rat.num_div_den r

lemma cuspOf_smul {c : ℤ} (hc : c ≠ 0) (v : Fin 2 → ℤ) : cuspOf (c • v) = cuspOf v := by
  simp only [cuspOf, Pi.smul_apply, smul_eq_mul, mul_eq_zero, hc, false_or]
  split_ifs with h
  · rfl
  · congr 1
    push_cast
    have hc' : (c : ℚ) ≠ 0 := by exact_mod_cast hc
    field_simp

/-- `fractional` on the level of vectors. -/
lemma fractional_eq_cuspOf {M : Matrix (Fin 2) (Fin 2) ℤ} (_hM : M.det ≠ 0) (x : Cusp) :
    fractional M x = cuspOf (M.mulVec (vecOf x)) := by
  rcases x with _ | r
  · simp only [fractional, cuspOf, vecOf, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, mul_zero, add_zero]
  · have hd : (r.den : ℤ) ≠ 0 := by exact_mod_cast r.den_ne_zero
    have hdq : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
    have hr' : (r : ℚ) * r.den = r.num := Rat.mul_den_eq_num r
    have key : ∀ a b : ℤ, ((a : ℚ) * r + b = 0 ↔ a * r.num + b * (r.den : ℤ) = 0) := by
      intro a b
      constructor
      · intro h
        have : ((a * r.num + b * (r.den : ℤ) : ℤ) : ℚ) = 0 := by
          push_cast; rw [← hr']; linear_combination (r.den : ℚ) * h
        exact_mod_cast this
      · intro h
        have h' : ((a * r.num + b * (r.den : ℤ) : ℤ) : ℚ) = 0 := by exact_mod_cast h
        push_cast at h'
        rw [← hr'] at h'
        have h2 : ((a : ℚ) * r + b) * r.den = 0 := by linear_combination h'
        exact (mul_eq_zero.mp h2).resolve_right hdq
    simp only [fractional, cuspOf, vecOf, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    by_cases h : (M 1 0 : ℚ) * r + M 1 1 = 0
    · rw [if_pos h, if_pos ((key _ _).mp h)]
    · have h' : ¬ (M 1 0 * r.num + M 1 1 * (r.den : ℤ) = 0) := fun h' => h ((key _ _).mpr h')
      rw [if_neg h, if_neg h']
      change ((((M 0 0 : ℚ) * r + M 0 1) / ((M 1 0 : ℚ) * r + M 1 1) : ℚ) : Cusp) =
        ((((M 0 0 * r.num + M 0 1 * (r.den : ℤ) : ℤ) : ℚ) /
          ((M 1 0 * r.num + M 1 1 * (r.den : ℤ) : ℤ) : ℚ) : ℚ) : Cusp)
      congr 1
      have h'' : ((M 1 0 * r.num + M 1 1 * (r.den : ℤ) : ℤ) : ℚ) ≠ 0 := by exact_mod_cast h'
      rw [div_eq_div_iff h h'']
      push_cast
      rw [← hr']
      ring

lemma cuspAct_eq_cuspOf (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (x : Cusp) :
    cuspAct γ x = cuspOf ((γ : Matrix (Fin 2) (Fin 2) ℤ).mulVec (vecOf x)) := by
  rw [← fractional_SL, fractional_eq_cuspOf (by simp)]

/-! ### Part B: linear forms and the `T^N`-invariants of `Sym^n` -/

/-- The linear form `v₀ X + v₁ Y` attached to a vector. -/
def lin (v : Fin 2 → ℤ) : Binary ℂ :=
  ((v 0 : ℤ) : ℂ) • MvPolynomial.X 0 + ((v 1 : ℤ) : ℂ) • MvPolynomial.X 1

lemma actAlg_X_eq (A : Matrix (Fin 2) (Fin 2) ℤ) (i : Fin 2) :
    actAlg A (MvPolynomial.X i) = ∑ a : Fin 2, ((A a i : ℤ) : ℂ) • (MvPolynomial.X a : Binary ℂ) := by
  rw [actAlg, MvPolynomial.aeval_X]

lemma act_lin (A : Matrix (Fin 2) (Fin 2) ℤ) (v : Fin 2 → ℤ) :
    act A (lin v) = lin (A.mulVec v) := by
  simp only [lin, act_eq_actAlg, map_add, map_smul, actAlg_X_eq, Fin.sum_univ_two,
    Matrix.mulVec, dotProduct]
  push_cast
  simp only [smul_add, smul_smul]
  module

lemma lin_smul (c : ℤ) (v : Fin 2 → ℤ) : lin (c • v) = (c : ℂ) • lin v := by
  simp only [lin, Pi.smul_apply, smul_eq_mul, Int.cast_mul, smul_add, smul_smul]

lemma lin_e0 : lin ![1, 0] = MvPolynomial.X 0 := by
  simp [lin]

lemma act_X0_pow (A : Matrix (Fin 2) (Fin 2) ℤ) (n : ℕ) :
    act A (MvPolynomial.X 0 ^ n) = lin (A.mulVec ![1, 0]) ^ n := by
  rw [act_eq_actAlg, map_pow, ← act_eq_actAlg, ← lin_e0, act_lin]

lemma act_C (γ : Matrix (Fin 2) (Fin 2) ℤ) (c : ℂ) : act γ (MvPolynomial.C c) = MvPolynomial.C c := by
  rw [act_eq_actAlg]; simp [actAlg]

/-- Evaluation of `act A P`. -/
lemma eval_act (A : Matrix (Fin 2) (Fin 2) ℤ) (P : Binary ℂ) (v : Fin 2 → ℂ) :
    MvPolynomial.eval v (act A P) =
      MvPolynomial.eval (fun i => ∑ a : Fin 2, ((A a i : ℤ) : ℂ) * v a) P := by
  induction P using MvPolynomial.induction_on with
  | C a => rw [act_C, MvPolynomial.eval_C, MvPolynomial.eval_C]
  | add p q hp hq => rw [map_add, MvPolynomial.eval_add, hp, hq, MvPolynomial.eval_add]
  | mul_X p i hp =>
    rw [act_eq_actAlg, map_mul, ← act_eq_actAlg, MvPolynomial.eval_mul, hp, actAlg_X_eq,
      MvPolynomial.eval_mul, MvPolynomial.eval_X]
    congr 1
    simp [MvPolynomial.eval_X]

/-- Homogeneity of degree `n` under scaling. -/
lemma eval_smul_of_mem_Sym {n : ℕ} {P : Binary ℂ} (hP : P ∈ Sym ℂ n) (c : ℂ) (v : Fin 2 → ℂ) :
    MvPolynomial.eval (c • v) P = c ^ n * MvPolynomial.eval v P := by
  rw [Sym_as_sum hP, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  rw [monomial_binaryExponent, MvPolynomial.eval_mul, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_pow, MvPolynomial.eval_pow, MvPolynomial.eval_X, MvPolynomial.eval_X,
    MvPolynomial.eval_mul, MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_pow,
    MvPolynomial.eval_pow, MvPolynomial.eval_X, MvPolynomial.eval_X, Pi.smul_apply, Pi.smul_apply,
    smul_eq_mul, smul_eq_mul, mul_pow, mul_pow]
  have : c ^ n = c ^ j * c ^ (n - j) := by rw [← pow_add, Nat.add_sub_cancel' (by omega)]
  rw [this]; ring

/-- The polynomial `t ↦ P(1, t)`. -/
def dehom (P : Binary ℂ) : Polynomial ℂ :=
  MvPolynomial.aeval (![Polynomial.C 1, Polynomial.X] : Fin 2 → Polynomial ℂ) P

lemma eval_dehom (P : Binary ℂ) (t : ℂ) :
    Polynomial.eval t (dehom P) = MvPolynomial.eval ![1, t] P := by
  unfold dehom
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, Polynomial.eval_add, hp, hq, MvPolynomial.eval_add]
  | mul_X p i hp =>
    rw [map_mul, MvPolynomial.aeval_X, Polynomial.eval_mul, hp, MvPolynomial.eval_mul,
      MvPolynomial.eval_X]
    congr 1
    fin_cases i <;> simp

/-- The `T^N`-invariants of `Sym^n` are the multiples of `X^n`. -/
theorem invariant_eq_smul_X_pow {N n : ℕ} (hN : 0 < N) {P : Binary ℂ} (hP : P ∈ Sym ℂ n)
    (h : act !![1, (N : ℤ); 0, 1] P = P) :
    P = MvPolynomial.eval ![1, 0] P • MvPolynomial.X 0 ^ n := by
  -- periodicity of `P(1, ·)`
  have hper : ∀ x y : ℂ, MvPolynomial.eval ![x, (N : ℂ) * x + y] P = MvPolynomial.eval ![x, y] P := by
    intro x y
    have hv : (fun i => ∑ a : Fin 2, ((!![1, (N : ℤ); 0, 1] a i : ℤ) : ℂ) * ![x, y] a) =
        ![x, (N : ℂ) * x + y] := by
      funext i; fin_cases i <;> simp [Fin.sum_univ_two]
    conv_rhs => rw [← h]
    rw [eval_act, hv]
  have hq : ∀ k : ℕ, Polynomial.eval ((k : ℂ) * N) (dehom P) = Polynomial.eval 0 (dehom P) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : ((k + 1 : ℕ) : ℂ) * N = (k : ℂ) * N + N := by push_cast; ring
      rw [e, eval_dehom, ← ih, eval_dehom]
      have := hper 1 ((k : ℂ) * N)
      rw [mul_one, add_comm] at this
      exact this
  have hconst : dehom P = Polynomial.C (Polynomial.eval 0 (dehom P)) := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (k : ℂ) * N) ?_ ?_
    · intro a b hab
      have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
      exact_mod_cast mul_right_cancel₀ hN' hab
    · intro k
      simp only [Set.mem_ofPred_eq, Polynomial.eval_C]
      exact hq k
  set c₀ : ℂ := Polynomial.eval 0 (dehom P) with hc₀
  have hc₀' : c₀ = MvPolynomial.eval ![1, 0] P := by rw [hc₀, eval_dehom]
  have hval : ∀ x y : ℂ, MvPolynomial.eval ![x, y] (MvPolynomial.X 0 * (P - MvPolynomial.C c₀ *
      MvPolynomial.X 0 ^ n)) = 0 := by
    intro x y
    by_cases hx : x = 0
    · simp [hx]
    · have h1 : MvPolynomial.eval ![x, y] P = x ^ n * c₀ := by
        have := eval_smul_of_mem_Sym hP x ![1, y / x]
        have h2 : x • ![(1 : ℂ), y / x] = ![x, y] := by
          ext i
          fin_cases i <;> simp
          field_simp
        rw [h2] at this
        rw [this]
        congr 1
        rw [← eval_dehom, hconst, Polynomial.eval_C]
      simp only [MvPolynomial.eval_mul, MvPolynomial.eval_sub, MvPolynomial.eval_C,
        MvPolynomial.eval_pow, MvPolynomial.eval_X, h1, Matrix.cons_val_zero]
      ring
  have hzero : MvPolynomial.X 0 * (P - MvPolynomial.C c₀ * MvPolynomial.X 0 ^ n) = 0 := by
    apply MvPolynomial.funext
    intro v
    have := hval (v 0) (v 1)
    rwa [show ![v 0, v 1] = v by ext i; fin_cases i <;> rfl] at this
  rcases mul_eq_zero.mp hzero with h0 | h0
  · exact absurd h0 (MvPolynomial.X_ne_zero 0)
  · rw [sub_eq_zero] at h0
    rw [← hc₀', MvPolynomial.smul_eq_C_mul]
    exact h0

/-! ### Part C: completing primitive vectors, and `Γ₁(N)`-transitivity -/

lemma exists_SL_first_col {v : Fin 2 → ℤ} (hv : IsCoprime (v 0) (v 1)) :
    ∃ A : SL(2, ℤ), (A : Matrix (Fin 2) (Fin 2) ℤ).mulVec ![1, 0] = v := by
  obtain ⟨s, t, hst⟩ := hv
  refine ⟨⟨!![v 0, -t; v 1, s], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of]; linear_combination hst
  · ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Reduction mod `N`. -/
abbrev red (N : ℕ) : SL(2, ℤ) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod N) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N))

lemma red_apply (N : ℕ) (M : SL(2, ℤ)) (i j : Fin 2) :
    (red N M : Matrix (Fin 2) (Fin 2) (ZMod N)) i j = ((M i j : ℤ) : ZMod N) := rfl

lemma mulVec_e0 (M : Matrix (Fin 2) (Fin 2) ℤ) : M.mulVec ![1, 0] = fun i => M i 0 := by
  ext i; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- `Γ₁(N)` acts transitively on primitive vectors with prescribed residues. -/
lemma exists_gamma1_mulVec {N : ℕ} (hN : 0 < N) {v w : Fin 2 → ℤ} (hv : IsCoprime (v 0) (v 1))
    (hw : IsCoprime (w 0) (w 1)) (j : ℤ)
    (h0 : ((w 0 : ℤ) : ZMod N) = v 0 + j * v 1) (h1 : ((w 1 : ℤ) : ZMod N) = v 1) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma1 N ∧ (δ : Matrix (Fin 2) (Fin 2) ℤ).mulVec v = w := by
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨A, hA'⟩ := exists_SL_first_col hv
  obtain ⟨B, hB'⟩ := exists_SL_first_col hw
  have hA := hA'
  have hB := hB'
  rw [mulVec_e0] at hA hB
  have hA0 : A 0 0 = v 0 := congrFun hA 0
  have hA1 : A 1 0 = v 1 := congrFun hA 1
  have hB0 : B 0 0 = w 0 := congrFun hB 0
  have hB1 : B 1 0 = w 1 := congrFun hB 1
  set U : Matrix.SpecialLinearGroup (Fin 2) (ZMod N) :=
    (red N B)⁻¹ * (red N (ModularGroup.T ^ j) * red N A) with hU
  have hcol : ∀ k, (red N (ModularGroup.T ^ j) * red N A :
      Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) k 0 = (red N B) k 0 := by
    intro k
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [red_apply, ModularGroup.coe_T_zpow]
    fin_cases k
    · simp [hA0, hA1, hB0, h0]
    · simp [hA1, hB1, h1]
  have hU0 : ∀ i, U i 0 = (1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) i 0 := by
    intro i
    have h1' : (1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) i 0 =
        ((red N B)⁻¹ * red N B) i 0 := by rw [inv_mul_cancel]
    rw [h1', hU, Matrix.SpecialLinearGroup.coe_mul ((red N B)⁻¹) (red N B), Matrix.mul_apply,
      Matrix.SpecialLinearGroup.coe_mul ((red N B)⁻¹) (red N (ModularGroup.T ^ j) * red N A),
      Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [hcol k]
  have hU00 : U 0 0 = 1 := by rw [hU0]; simp
  have hU10 : U 1 0 = 0 := by rw [hU0]; simp
  have hU11 : U 1 1 = 1 := by
    have hdet := U.2
    rw [Matrix.det_fin_two, hU00, hU10] at hdet
    simpa using hdet
  set m : ℤ := ((U 0 1).val : ℤ) with hm
  have hmU : ((m : ℤ) : ZMod N) = U 0 1 := by rw [hm, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hTm : red N (ModularGroup.T ^ m) = U := by
    apply Matrix.SpecialLinearGroup.ext
    intro i k
    rw [red_apply, ModularGroup.coe_T_zpow]
    fin_cases i <;> fin_cases k
    · simp [hU00]
    · simp [hmU]
    · simp [hU10]
    · simp [hU11]
  refine ⟨B * ModularGroup.T ^ m * A⁻¹, ?_, ?_⟩
  · have hred : red N (B * ModularGroup.T ^ m * A⁻¹) = red N (ModularGroup.T ^ j) := by
      rw [map_mul, map_mul, map_inv, hTm, hU]
      group
    rw [Gamma1_mem]
    have e := fun i k => congrArg
      (fun M : Matrix.SpecialLinearGroup (Fin 2) (ZMod N) => (M : Matrix (Fin 2) (Fin 2) (ZMod N)) i k)
      hred
    simp only [red_apply, ModularGroup.coe_T_zpow] at e
    refine ⟨?_, ?_, ?_⟩
    · have := e 0 0; simpa using this
    · have := e 1 1; simpa using this
    · have := e 1 0; simpa using this
  · have hAinv : ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).mulVec v = ![1, 0] := by
      rw [← hA', Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    have hT : ((ModularGroup.T ^ m : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).mulVec ![1, 0] =
        ![1, 0] := by
      rw [ModularGroup.coe_T_zpow, mulVec_e0]; ext i; fin_cases i <;> simp
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hAinv, hT, hB']

/-! ### Part D: the eigen-structure of boundary data -/

lemma cuspAct_mul (γ δ : SL(2, ℤ)) (x : Cusp) : cuspAct (γ * δ) x = cuspAct γ (cuspAct δ x) := by
  simp only [cuspAct, map_mul, mul_smul]

lemma cuspAct_one (x : Cusp) : cuspAct 1 x = x := by
  simp [cuspAct]

lemma red_T_pow_N (N : ℕ) : red N (ModularGroup.T ^ (N : ℤ)) = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i k
  rw [red_apply, ModularGroup.coe_T_zpow]
  fin_cases i <;> fin_cases k <;> simp

lemma conj_T_pow_mem_Gamma1 {N : ℕ} (A : SL(2, ℤ)) :
    A * ModularGroup.T ^ (N : ℤ) * A⁻¹ ∈ Gamma1 N := by
  have hred : red N (A * ModularGroup.T ^ (N : ℤ) * A⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, red_T_pow_N, mul_one, mul_inv_cancel]
  rw [Gamma1_mem]
  have e := fun i k => congrArg
    (fun M : SL(2, ZMod N) => (M : Matrix (Fin 2) (Fin 2) (ZMod N)) i k) hred
  simp only [red_apply] at e
  exact ⟨by simpa using e 0 0, by simpa using e 1 1, by simpa using e 1 0⟩

lemma cuspAct_T_pow_infty (N : ℕ) :
    cuspAct (ModularGroup.T ^ (N : ℤ)) OnePoint.infty = OnePoint.infty := by
  rw [cuspAct_eq_cuspOf, vecOf_infty, ModularGroup.coe_T_zpow, mulVec_e0]
  have : (fun i => (!![1, (N : ℤ); 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) i 0) = ![1, 0] := by
    ext i; fin_cases i <;> simp
  rw [this]
  simp [cuspOf]

/-- Boundary data are "eigen": `Φ x` is a multiple of `ℓ_v^n`, `v` the primitive vector of `x`. -/
lemma eigen_of_datum {N n : ℕ} (hN : 0 < N) {Φ : Cusp → Binary ℂ} (hΦ : IsBoundaryDatum N n Φ)
    (x : Cusp) : ∃ c : ℂ, Φ x = c • lin (vecOf x) ^ n := by
  obtain ⟨A, hA⟩ := exists_SL_first_col (vecOf_isCoprime x)
  have hx : cuspAct A OnePoint.infty = x := by
    rw [cuspAct_eq_cuspOf, vecOf_infty, hA, cuspOf_vecOf]
  set γ : SL(2, ℤ) := A * ModularGroup.T ^ (N : ℤ) * A⁻¹ with hγ
  have hγmem : γ ∈ Gamma1 N := conj_T_pow_mem_Gamma1 A
  have hγx : cuspAct γ x = x := by
    rw [hγ, ← hx, cuspAct_mul, cuspAct_mul, ← cuspAct_mul A⁻¹ A OnePoint.infty, inv_mul_cancel,
      cuspAct_one, cuspAct_T_pow_infty]
  set Ψ : Binary ℂ := act ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (Φ x) with hΨ
  have hΨmem : Ψ ∈ Sym ℂ n := act_mem_Sym _ (hΦ.1 x)
  have hinv : act !![1, (N : ℤ); 0, 1] Ψ = Ψ := by
    have heq : act (γ : Matrix (Fin 2) (Fin 2) ℤ) (Φ x) = Φ x := by
      have := hΦ.2 ⟨γ, hγmem⟩ x
      rw [hγx] at this
      exact this.symm
    have hmat : ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) =
        !![1, (N : ℤ); 0, 1] * ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [hγ, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ← mul_assoc,
        ← mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, one_mul, ModularGroup.coe_T_zpow]
    rw [hΨ, act_act, ← hmat, ← act_act, heq]
  have hΨeq := invariant_eq_smul_X_pow hN hΨmem hinv
  refine ⟨MvPolynomial.eval ![1, 0] Ψ, ?_⟩
  have hΦx : Φ x = act (A : Matrix (Fin 2) (Fin 2) ℤ) Ψ := by
    rw [hΨ, act_act, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, act_one]
  rw [hΦx]
  conv_lhs => rw [hΨeq]
  rw [map_smul, act_X0_pow, hA]

/-- The general transport lemma for one Hecke representative. -/
lemma term_general {N n : ℕ} (hN : 0 < N) {Φ : Cusp → Binary ℂ} (hΦ : IsBoundaryDatum N n Φ)
    (x : Cusp) {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M.det ≠ 0) {w : Fin 2 → ℤ}
    (hw : IsCoprime (w 0) (w 1)) {g : ℤ} (hg : g ≠ 0) (hMv : M.mulVec (vecOf x) = g • w)
    {c : ℤ} (hadj : M.adjugate.mulVec w = c • vecOf x)
    (j : ℤ) (h0 : ((w 0 : ℤ) : ZMod N) = vecOf x 0 + j * vecOf x 1)
    (h1 : ((w 1 : ℤ) : ZMod N) = vecOf x 1) :
    act M.adjugate (Φ (fractional M x)) = ((c : ℂ) ^ n) • Φ x := by
  obtain ⟨δ, hδ, hδv⟩ := exists_gamma1_mulVec hN (vecOf_isCoprime x) hw j h0 h1
  have hfx : fractional M x = cuspAct δ x := by
    rw [fractional_eq_cuspOf hM, hMv, cuspOf_smul hg, cuspAct_eq_cuspOf, hδv]
  have heq : Φ (cuspAct δ x) = act (δ : Matrix (Fin 2) (Fin 2) ℤ) (Φ x) := hΦ.2 ⟨δ, hδ⟩ x
  obtain ⟨c₀, hc₀⟩ := eigen_of_datum hN hΦ x
  rw [hfx, heq, act_act, hc₀, map_smul, act_eq_actAlg, map_pow, ← act_eq_actAlg,
    act_lin, ← Matrix.mulVec_mulVec, hδv, hadj, lin_smul, smul_pow, smul_smul, smul_smul,
    mul_comm]

lemma adj_mulVec_mulVec (M : Matrix (Fin 2) (Fin 2) ℤ) (v : Fin 2 → ℤ) :
    M.adjugate.mulVec (M.mulVec v) = M.det • v := by
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul]
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Matrix.one_apply]

lemma term_β {N n : ℕ} (hN : 0 < N) {Φ : Cusp → Binary ℂ} (hΦ : IsBoundaryDatum N n Φ)
    {l : ℕ} (hl : l.Prime) (hlN : (l : ZMod N) = 1) (x : Cusp) (b : ℤ) :
    act (Matrix.adjugate !![1, b; 0, (l : ℤ)]) (Φ (fractional !![1, b; 0, (l : ℤ)] x)) =
      (if (l : ℤ) ∣ vecOf x 0 + b * vecOf x 1 then (1 : ℂ) else (l : ℂ) ^ n) • Φ x := by
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hdet : (!![1, b; 0, (l : ℤ)]).det = l := by simp [Matrix.det_fin_two_of]
  have hdet' : (!![1, b; 0, (l : ℤ)]).det ≠ 0 := by rw [hdet]; exact hl0
  have hv := vecOf_isCoprime x
  have hlN' : ((l : ℤ) : ZMod N) = 1 := by rw [Int.cast_natCast]; exact hlN
  have hmul : (!![1, b; 0, (l : ℤ)]).mulVec (vecOf x) =
      ![vecOf x 0 + b * vecOf x 1, l * vecOf x 1] := by
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hadj : (!![1, b; 0, (l : ℤ)]).adjugate = !![(l : ℤ), -b; 0, 1] := by
    rw [Matrix.adjugate_fin_two_of]; simp
  split_ifs with hdvd
  · obtain ⟨k, hk⟩ := hdvd
    have hw : IsCoprime (![k, vecOf x 1] 0) (![k, vecOf x 1] 1) := by
      have : IsCoprime ((l : ℤ) * k) (vecOf x 1) := by rw [← hk]; exact hv.add_mul_right_left b
      simpa using this.of_mul_left_right
    have hMv : (!![1, b; 0, (l : ℤ)]).mulVec (vecOf x) = (l : ℤ) • ![k, vecOf x 1] := by
      rw [hmul, hk]; ext i; fin_cases i <;> simp
    have hadj' : (!![1, b; 0, (l : ℤ)]).adjugate.mulVec ![k, vecOf x 1] = (1 : ℤ) • vecOf x := by
      rw [hadj]; ext i; fin_cases i
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]; linear_combination -hk
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have h0 : ((![k, vecOf x 1] 0 : ℤ) : ZMod N) = vecOf x 0 + b * vecOf x 1 := by
      have := congrArg (Int.cast : ℤ → ZMod N) hk
      push_cast at this
      rw [hlN, one_mul] at this
      simpa using this.symm
    have h1 : ((![k, vecOf x 1] 1 : ℤ) : ZMod N) = vecOf x 1 := by simp
    rw [term_general hN hΦ x hdet' hw hl0 hMv hadj' b h0 h1]
    simp
  · have hw : IsCoprime ((!![1, b; 0, (l : ℤ)]).mulVec (vecOf x) 0)
        ((!![1, b; 0, (l : ℤ)]).mulVec (vecOf x) 1) := by
      rw [hmul]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      refine IsCoprime.mul_right ?_ (hv.add_mul_right_left b)
      have hlp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
      exact ((Irreducible.coprime_iff_not_dvd hlp.irreducible).mpr hdvd).symm
    have hMv : (!![1, b; 0, (l : ℤ)]).mulVec (vecOf x) =
        (1 : ℤ) • (!![1, b; 0, (l : ℤ)]).mulVec (vecOf x) := by rw [one_smul]
    have hadj' : (!![1, b; 0, (l : ℤ)]).adjugate.mulVec ((!![1, b; 0, (l : ℤ)]).mulVec (vecOf x)) =
        (l : ℤ) • vecOf x := by
      rw [adj_mulVec_mulVec, hdet]
    have h0 : (((!![1, b; 0, (l : ℤ)]).mulVec (vecOf x) 0 : ℤ) : ZMod N) =
        vecOf x 0 + b * vecOf x 1 := by
      rw [hmul]; simp
    have h1 : (((!![1, b; 0, (l : ℤ)]).mulVec (vecOf x) 1 : ℤ) : ZMod N) = vecOf x 1 := by
      rw [hmul]; simp [hlN]
    rw [term_general hN hΦ x hdet' hw one_ne_zero hMv hadj' b h0 h1]
    simp

lemma term_α {N n : ℕ} (hN : 0 < N) {Φ : Cusp → Binary ℂ} (hΦ : IsBoundaryDatum N n Φ)
    {l : ℕ} (hl : l.Prime) (hlN : (l : ZMod N) = 1) (x : Cusp) :
    act (Matrix.adjugate !![(l : ℤ), 0; 0, 1]) (Φ (fractional !![(l : ℤ), 0; 0, 1] x)) =
      (if (l : ℤ) ∣ vecOf x 1 then (1 : ℂ) else (l : ℂ) ^ n) • Φ x := by
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hdet : (!![(l : ℤ), 0; 0, 1]).det = l := by simp [Matrix.det_fin_two_of]
  have hdet' : (!![(l : ℤ), 0; 0, 1]).det ≠ 0 := by rw [hdet]; exact hl0
  have hv := vecOf_isCoprime x
  have hlN' : ((l : ℤ) : ZMod N) = 1 := by rw [Int.cast_natCast]; exact hlN
  have hmul : (!![(l : ℤ), 0; 0, 1]).mulVec (vecOf x) = ![l * vecOf x 0, vecOf x 1] := by
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hadj : (!![(l : ℤ), 0; 0, 1]).adjugate = !![1, 0; 0, (l : ℤ)] := by
    rw [Matrix.adjugate_fin_two_of]; simp
  split_ifs with hdvd
  · obtain ⟨k, hk⟩ := hdvd
    have hw : IsCoprime (![vecOf x 0, k] 0) (![vecOf x 0, k] 1) := by
      have : IsCoprime (vecOf x 0) ((l : ℤ) * k) := by rw [← hk]; exact hv
      simpa using this.of_mul_right_right
    have hMv : (!![(l : ℤ), 0; 0, 1]).mulVec (vecOf x) = (l : ℤ) • ![vecOf x 0, k] := by
      rw [hmul, hk]; ext i; fin_cases i <;> simp
    have hadj' : (!![(l : ℤ), 0; 0, 1]).adjugate.mulVec ![vecOf x 0, k] = (1 : ℤ) • vecOf x := by
      rw [hadj]; ext i; fin_cases i
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hk]
    have h0 : ((![vecOf x 0, k] 0 : ℤ) : ZMod N) = vecOf x 0 + ((0 : ℤ) : ZMod N) * vecOf x 1 := by
      simp
    have h1 : ((![vecOf x 0, k] 1 : ℤ) : ZMod N) = vecOf x 1 := by
      have := congrArg (Int.cast : ℤ → ZMod N) hk
      push_cast at this
      rw [hlN, one_mul] at this
      simpa using this.symm
    rw [term_general hN hΦ x hdet' hw hl0 hMv hadj' 0 h0 h1]
    simp
  · have hw : IsCoprime ((!![(l : ℤ), 0; 0, 1]).mulVec (vecOf x) 0)
        ((!![(l : ℤ), 0; 0, 1]).mulVec (vecOf x) 1) := by
      rw [hmul]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      refine IsCoprime.mul_left ?_ hv
      have hlp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
      exact (Irreducible.coprime_iff_not_dvd hlp.irreducible).mpr hdvd
    have hMv : (!![(l : ℤ), 0; 0, 1]).mulVec (vecOf x) =
        (1 : ℤ) • (!![(l : ℤ), 0; 0, 1]).mulVec (vecOf x) := by rw [one_smul]
    have hadj' : (!![(l : ℤ), 0; 0, 1]).adjugate.mulVec ((!![(l : ℤ), 0; 0, 1]).mulVec (vecOf x)) =
        (l : ℤ) • vecOf x := by
      rw [adj_mulVec_mulVec, hdet]
    have h0 : (((!![(l : ℤ), 0; 0, 1]).mulVec (vecOf x) 0 : ℤ) : ZMod N) =
        vecOf x 0 + ((0 : ℤ) : ZMod N) * vecOf x 1 := by
      rw [hmul]; simp [hlN]
    have h1 : (((!![(l : ℤ), 0; 0, 1]).mulVec (vecOf x) 1 : ℤ) : ZMod N) = vecOf x 1 := by
      rw [hmul]; simp
    rw [term_general hN hΦ x hdet' hw one_ne_zero hMv hadj' 0 h0 h1]
    simp

/-! ### Part E: counting and assembly -/

/-- The `Fin l ≃ ZMod l` equivalence. -/
def finEquivZMod {l : ℕ} [NeZero l] : Fin l ≃ ZMod l where
  toFun i := (i.val : ZMod l)
  invFun z := ⟨z.val, z.val_lt⟩
  left_inv i := by ext; simp [ZMod.val_natCast, Nat.mod_eq_of_lt i.2]
  right_inv z := by simp

lemma count_sum {l : ℕ} (hl : l.Prime) {v0 v1 : ℤ} (hv : IsCoprime v0 v1) (n : ℕ) :
    (∑ b : Fin l, (if (l : ℤ) ∣ v0 + (b.val : ℤ) * v1 then (1 : ℂ) else (l : ℂ) ^ n)) +
      (if (l : ℤ) ∣ v1 then (1 : ℂ) else (l : ℂ) ^ n) = ((1 + l ^ (n + 1) : ℕ) : ℂ) := by
  have := Fact.mk hl
  have : NeZero l := ⟨hl.ne_zero⟩
  have hdvd : ∀ z : ℤ, (l : ℤ) ∣ z ↔ ((z : ZMod l) = 0) := fun z =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd z l).symm
  by_cases h1 : ((v1 : ℤ) : ZMod l) = 0
  · have hv0 : ((v0 : ℤ) : ZMod l) ≠ 0 := by
      obtain ⟨s, t, hst⟩ := hv
      intro h0
      have := congrArg (Int.cast : ℤ → ZMod l) hst
      push_cast at this
      rw [h0, h1] at this
      simp at this
    rw [if_pos ((hdvd v1).mpr h1)]
    have hno : ∀ b : Fin l, ¬ ((l : ℤ) ∣ v0 + (b.val : ℤ) * v1) := by
      intro b hb
      rw [hdvd] at hb
      push_cast at hb
      rw [h1, mul_zero, add_zero] at hb
      exact hv0 hb
    simp only [hno, if_false, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  · rw [if_neg (fun h => h1 ((hdvd v1).mp h))]
    have hcond : ∀ b : Fin l, ((l : ℤ) ∣ v0 + (b.val : ℤ) * v1) ↔
        ((b.val : ℕ) : ZMod l) = -(v0 : ZMod l) * ((v1 : ZMod l))⁻¹ := by
      intro b
      rw [hdvd]
      push_cast
      constructor
      · intro h
        field_simp
        linear_combination h
      · intro h
        rw [h]
        field_simp
        ring
    have hsum : (∑ b : Fin l, (if (l : ℤ) ∣ v0 + (b.val : ℤ) * v1 then (1 : ℂ) else (l : ℂ) ^ n)) =
        ∑ z : ZMod l, (if z = -(v0 : ZMod l) * ((v1 : ZMod l))⁻¹ then (1 : ℂ) else (l : ℂ) ^ n) := by
      refine Fintype.sum_equiv finEquivZMod _ _ fun b => ?_
      simp only [hcond b]
      rfl
    rw [hsum]
    have hsplit : ∀ z : ZMod l, (if z = -(v0 : ZMod l) * ((v1 : ZMod l))⁻¹ then (1 : ℂ) else (l : ℂ) ^ n)
        = (l : ℂ) ^ n + (if z = -(v0 : ZMod l) * ((v1 : ZMod l))⁻¹ then 1 - (l : ℂ) ^ n else 0) := by
      intro z; split_ifs <;> ring
    simp only [hsplit, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    push_cast
    ring

/-- The main theorem. -/
theorem boundary_hecke_cusp_sum_at_one_proof {N n : ℕ} (hN : 0 < N)
    (Φ : Cusp → Binary ℂ) (hΦ : IsBoundaryDatum N n Φ)
    (l : ℕ) (hl : l.Prime) (hlN : (l : ZMod N) = 1) (x : Cusp) :
    (∑ b : Fin l, act (Matrix.adjugate !![1, (b.val : ℤ); 0, (l : ℤ)])
        (Φ (fractional !![1, (b.val : ℤ); 0, (l : ℤ)] x))) +
      act (Matrix.adjugate !![(l : ℤ), 0; 0, 1]) (Φ (fractional !![(l : ℤ), 0; 0, 1] x)) =
      ((1 + l^(n+1) : ℕ) : ℂ) • Φ x := by
  rw [Finset.sum_congr rfl (fun b _ => term_β hN hΦ hl hlN x (b.val : ℤ)), term_α hN hΦ hl hlN x,
    ← Finset.sum_smul, ← add_smul, count_sum hl (vecOf_isCoprime x) n]

end MTT.Cohomology

open MTT.Cohomology

theorem solution
    {N n : ℕ} (hN : 0 < N)
    (Φ : Cusp → Binary ℂ) (hΦ : IsBoundaryDatum N n Φ)
    (l : ℕ) (hl : l.Prime) (hlN : (l : ZMod N) = 1) (x : Cusp) :
    (∑ b : Fin l,
      act (Matrix.adjugate !![1, (b.val : ℤ); 0, (l : ℤ)])
        (Φ (fractional !![1, (b.val : ℤ); 0, (l : ℤ)] x))) +
      act (Matrix.adjugate !![(l : ℤ), 0; 0, 1])
        (Φ (fractional !![(l : ℤ), 0; 0, 1] x)) =
      ((1 + l^(n+1) : ℕ) : ℂ) • Φ x :=
  MTT.Cohomology.boundary_hecke_cusp_sum_at_one_proof hN Φ hΦ l hl hlN x
