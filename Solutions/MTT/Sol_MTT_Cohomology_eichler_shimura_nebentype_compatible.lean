import Theorems.MTT.Thm_MTT_Cohomology_eichler_shimura_direct
import Theorems.MTT.Thm_MTT_Cohomology_cuspPrimitive_slash_relation
import Theorems.MTT.Thm_MTT_exists_cuspForm_slash_gamma0
import Definitions.MTT.Def_MTT_Cohomology_Integration
import Definitions.MTT.Def_MTT_Cohomology_Boundary
import Mathlib.RingTheory.Flat.Basic
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

namespace MTT.Cohomology

lemma binaryExponent_apply_zero (n j : ℕ) : binaryExponent n j 0 = j := by
  simp [binaryExponent]

lemma coeff_cuspPeriodPolynomial {N k : ℕ} (hk : 2 ≤ k) (f : CuspForm (MTT.GammaOne N) (k : ℤ))
    (r : ℚ) {j : ℕ} (hj : j ≤ k - 2) :
    AddMonoidAlgebra.coeff (cuspPeriodPolynomial f r) (binaryExponent (k - 2) j) =
      ((k - 2).choose j : ℂ) * MTT.modularIntegral f (Polynomial.X ^ j) r := by
  rw [cuspPeriodPolynomial, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [ite_eq_right]
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
    (h : ∀ j ≤ n, AddMonoidAlgebra.coeff P (binaryExponent n j) =
      AddMonoidAlgebra.coeff Q (binaryExponent n j)) : P = Q := by
  rw [MvPolynomial.mem_homogeneousSubmodule] at hP hQ
  ext m
  by_cases hm : AddMonoidAlgebra.coeff P m = 0 ∧ AddMonoidAlgebra.coeff Q m = 0
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
      MvPolynomial.monomial (binaryExponent n j) (AddMonoidAlgebra.coeff P (binaryExponent n j)) := by
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
      rw [ite_eq_right]
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
  have := ((MvPolynomial.isHomogeneous_C (Fin 2) (AddMonoidAlgebra.coeff P (binaryExponent n j))).mul
    ((actAlg_X_isHomogeneous γ 0).pow j)).mul ((actAlg_X_isHomogeneous γ 1).pow (n - j))
  have e : 0 + 1 * j + 1 * (n - j) = n := by omega
  rw [e] at this
  exact this

/-! ### Γ₀(N) and the reflection -/

lemma det_entries (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := γ.2; rwa [Matrix.det_fin_two] at this

/-- `Γ₁(N)` is normal in `Γ₀(N)`. -/
lemma conj_mem_Gamma1 {N : ℕ} (γ : CongruenceSubgroup.Gamma0 N)
    {δ : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hδ : δ ∈ CongruenceSubgroup.Gamma1 N) :
    γ.val * δ * γ.val⁻¹ ∈ CongruenceSubgroup.Gamma1 N := by
  rw [CongruenceSubgroup.Gamma1, Subgroup.mem_map] at hδ ⊢
  obtain ⟨δ', -, rfl⟩ := hδ
  refine ⟨⟨γ * δ'.val * γ⁻¹, ?_⟩, Subgroup.mem_top _, ?_⟩
  · exact (MonoidHom.normal_ker (CongruenceSubgroup.Gamma0Map N)).conj_mem δ'.val δ'.property γ
  · simp

/-- The conjugate `ρ γ ρ` of `γ ∈ Γ₀(N)` by the reflection `ρ = diag(-1, 1)`. -/
def conjRefl {N : ℕ} (γ : CongruenceSubgroup.Gamma0 N) : CongruenceSubgroup.Gamma0 N :=
  ⟨⟨!![γ.val 0 0, -γ.val 0 1; -γ.val 1 0, γ.val 1 1], by
      rw [Matrix.det_fin_two_of]; linear_combination det_entries γ.val⟩,
    CongruenceSubgroup.Gamma0_mem.mpr (by
      change ((-(γ.val 1 0) : ℤ) : ZMod N) = 0
      rw [Int.cast_neg, CongruenceSubgroup.Gamma0_mem.mp γ.2, neg_zero])⟩

lemma conjRefl_00 {N : ℕ} (γ : CongruenceSubgroup.Gamma0 N) : (conjRefl γ).val 0 0 = γ.val 0 0 := rfl
lemma conjRefl_01 {N : ℕ} (γ : CongruenceSubgroup.Gamma0 N) : (conjRefl γ).val 0 1 = -γ.val 0 1 := rfl
lemma conjRefl_10 {N : ℕ} (γ : CongruenceSubgroup.Gamma0 N) : (conjRefl γ).val 1 0 = -γ.val 1 0 := rfl
lemma conjRefl_11 {N : ℕ} (γ : CongruenceSubgroup.Gamma0 N) : (conjRefl γ).val 1 1 = γ.val 1 1 := rfl

lemma refl_mul_refl : (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) * !![-1, 0; 0, 1] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two] <;> simp

lemma refl_mul_conjRefl {N : ℕ} (γ : CongruenceSubgroup.Gamma0 N) :
    (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) * ((conjRefl γ).val : Matrix (Fin 2) (Fin 2) ℤ) =
      (γ.val : Matrix (Fin 2) (Fin 2) ℤ) * !![-1, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp [conjRefl]

lemma mapGL_apply' {N : ℕ} (γ : CongruenceSubgroup.Gamma0 N) (i j : Fin 2) :
    ((Matrix.SpecialLinearGroup.mapGL ℚ γ.val : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j =
      ((γ.val i j : ℤ) : ℚ) := by
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  simp

lemma cuspAct_infty {N : ℕ} (γ : CongruenceSubgroup.Gamma0 N) :
    cuspAct γ.val OnePoint.infty =
      if ((γ.val 1 0 : ℤ) : ℚ) = 0 then OnePoint.infty
      else ((((γ.val 0 0 : ℤ) : ℚ) / ((γ.val 1 0 : ℤ) : ℚ) : ℚ) : Cusp) := by
  unfold cuspAct
  rw [OnePoint.smul_infty_eq_ite]
  simp only [mapGL_apply']

lemma cuspAct_coe {N : ℕ} (γ : CongruenceSubgroup.Gamma0 N) (r : ℚ) :
    cuspAct γ.val (r : Cusp) =
      if ((γ.val 1 0 : ℤ) : ℚ) * r + ((γ.val 1 1 : ℤ) : ℚ) = 0 then OnePoint.infty
      else (((((γ.val 0 0 : ℤ) : ℚ) * r + ((γ.val 0 1 : ℤ) : ℚ)) /
        (((γ.val 1 0 : ℤ) : ℚ) * r + ((γ.val 1 1 : ℤ) : ℚ)) : ℚ) : Cusp) := by
  unfold cuspAct
  rw [OnePoint.smul_some_eq_ite]
  simp only [mapGL_apply']

lemma fractional_refl_cuspAct {N : ℕ} (γ : CongruenceSubgroup.Gamma0 N) (x : Cusp) :
    fractional !![-1, 0; 0, 1] (cuspAct γ.val x) =
      cuspAct (conjRefl γ).val (fractional !![-1, 0; 0, 1] x) := by
  rcases x with _ | r
  · change fractional !![-1, 0; 0, 1] (cuspAct γ.val OnePoint.infty) =
      cuspAct (conjRefl γ).val (fractional !![-1, 0; 0, 1] OnePoint.infty)
    rw [fractional_refl_infty, cuspAct_infty, cuspAct_infty, conjRefl_10, conjRefl_00]
    push_cast
    by_cases hc : ((γ.val 1 0 : ℤ) : ℚ) = 0
    · rw [ite_eq_left hc, ite_eq_left (neg_eq_zero.mpr hc), fractional_refl_infty]
    · rw [ite_eq_right hc, ite_eq_right (neg_ne_zero.mpr hc), fractional_refl_coe, div_neg]
  · change fractional !![-1, 0; 0, 1] (cuspAct γ.val (r : Cusp)) =
      cuspAct (conjRefl γ).val (fractional !![-1, 0; 0, 1] (r : Cusp))
    rw [fractional_refl_coe, cuspAct_coe, cuspAct_coe, conjRefl_10, conjRefl_11, conjRefl_00,
      conjRefl_01]
    push_cast
    by_cases hc : ((γ.val 1 0 : ℤ) : ℚ) * r + ((γ.val 1 1 : ℤ) : ℚ) = 0
    · have hc' : -((γ.val 1 0 : ℤ) : ℚ) * -r + ((γ.val 1 1 : ℤ) : ℚ) = 0 := by
        linear_combination hc
      rw [ite_eq_left hc, ite_eq_left hc', fractional_refl_infty]
    · have hc' : ¬ (-((γ.val 1 0 : ℤ) : ℚ) * -r + ((γ.val 1 1 : ℤ) : ℚ) = 0) := fun h =>
        hc (by linear_combination h)
      rw [ite_eq_right hc, ite_eq_right hc', fractional_refl_coe]
      congr 1
      field_simp
      ring

/-! ### Transport of the three summands along `Γ₀(N)` -/

lemma cuspAct_mul (γ δ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (x : Cusp) :
    cuspAct (γ * δ) x = cuspAct γ (cuspAct δ x) := by
  unfold cuspAct; rw [map_mul, mul_smul]

/-- The class of `g` at `(∞, s)` is the cusp primitive, and the cocycle relation. -/
lemma class_eq_primitive {N k : ℕ} (hk : 2 ≤ k) (g : CuspForm (MTT.GammaOne N) (k : ℤ))
    (φ : Hc N (k-2) ℂ) (hφ : IntegralClass g φ) (x y : Cusp) :
    φ.val (x, y) = cuspPrimitive g y - cuspPrimitive g x := by
  obtain ⟨hsym, hcocy, -⟩ := φ.2
  have hval : ∀ s : Cusp, φ.val (OnePoint.infty, s) = cuspPrimitive g s := by
    intro s
    rcases s with _ | r
    · exact add_eq_left.mp (hcocy OnePoint.infty OnePoint.infty OnePoint.infty)
    · apply Sym_ext (hsym _ _) (cuspPeriodPolynomial_mem_Sym hk g r)
      intro j hj
      change evaluation j r φ = _
      rw [hφ j r hj, coeff_cuspPeriodPolynomial hk g r hj]
  have := hcocy OnePoint.infty x y
  rw [← hval y, ← hval x, ← this]; abel

lemma transport_holo {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ)
    (hI : ∀ f, IntegralClass f (I f)) (g g' : CuspForm (MTT.GammaOne N) (k : ℤ))
    (γ : CongruenceSubgroup.Gamma0 N)
    (hg' : ∀ z : UpperHalfPlane,
      g ((Matrix.SpecialLinearGroup.mapGL ℝ γ.val) • z) =
        (((γ.val 1 0 : ℤ) : ℂ) * z + ((γ.val 1 1 : ℤ) : ℂ)) ^ k * g' z)
    (x y : Cusp) :
    (I g).val (cuspAct γ.val x, cuspAct γ.val y) = act γ.val.val ((I g').val (x, y)) := by
  rw [class_eq_primitive hk g (I g) (hI g), class_eq_primitive hk g' (I g') (hI g'),
    MTT.Cohomology.cuspPrimitive_slash_relation hN hk g g' γ hg' y,
    MTT.Cohomology.cuspPrimitive_slash_relation hN hk g g' γ hg' x, map_sub]
  abel

lemma transport_refl {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ)
    (hI : ∀ f, IntegralClass f (I f)) (h h' : CuspForm (MTT.GammaOne N) (k : ℤ))
    (γ : CongruenceSubgroup.Gamma0 N)
    (hh' : ∀ z : UpperHalfPlane,
      h ((Matrix.SpecialLinearGroup.mapGL ℝ (conjRefl γ).val) • z) =
        ((((conjRefl γ).val 1 0 : ℤ) : ℂ) * z + (((conjRefl γ).val 1 1 : ℤ) : ℂ)) ^ k * h' z)
    (x y : Cusp) :
    reflection (I h).val (cuspAct γ.val x, cuspAct γ.val y) =
      act γ.val.val (reflection (I h').val (x, y)) := by
  simp only [reflection]
  rw [fractional_refl_cuspAct, fractional_refl_cuspAct,
    transport_holo hN hk I hI h h' (conjRefl γ) hh', act_act, refl_mul_conjRefl, ← act_act]

/-- The transported boundary datum `x ↦ adj(γ) · Φ(γ x)`. -/
def transportDatum {N : ℕ} (γ : CongruenceSubgroup.Gamma0 N) (Φ : Cusp → Binary ℂ) :
    Cusp → Binary ℂ :=
  fun x => act (Matrix.adjugate γ.val.val) (Φ (cuspAct γ.val x))

lemma transportDatum_isBoundaryDatum {N n : ℕ} (γ : CongruenceSubgroup.Gamma0 N)
    {Φ : Cusp → Binary ℂ} (hΦ : IsBoundaryDatum N n Φ) :
    IsBoundaryDatum N n (transportDatum γ Φ) := by
  refine ⟨fun x => act_mem_Sym _ (hΦ.1 _), fun δ x => ?_⟩
  unfold transportDatum
  have hmem := conj_mem_Gamma1 γ δ.2
  have h1 : cuspAct γ.val (cuspAct δ.val x) =
      cuspAct (γ.val * δ.val * γ.val⁻¹) (cuspAct γ.val x) := by
    rw [← cuspAct_mul, ← cuspAct_mul, mul_assoc, inv_mul_cancel, mul_one]
  have hM : Matrix.adjugate γ.val.val *
      ((γ.val * δ.val * γ.val⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
      δ.val.val * Matrix.adjugate γ.val.val := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, ← mul_assoc, ← mul_assoc, Matrix.adjugate_mul, γ.val.2,
      one_smul, one_mul]
  rw [h1, hΦ.2 ⟨_, hmem⟩, act_act, act_act, hM]

lemma boundaryCochain_transport {N : ℕ} (γ : CongruenceSubgroup.Gamma0 N) (Φ : Cusp → Binary ℂ)
    (x y : Cusp) :
    boundaryCochain Φ (cuspAct γ.val x, cuspAct γ.val y) =
      act γ.val.val (boundaryCochain (transportDatum γ Φ) (x, y)) := by
  simp only [boundaryCochain, transportDatum, map_sub, act_act, Matrix.mul_adjugate, γ.val.2,
    one_smul, act_one]

lemma boundaryCochain_sub (Φ Ψ : Cusp → Binary ℂ) :
    boundaryCochain (Φ - Ψ) = boundaryCochain Φ - boundaryCochain Ψ := by
  funext D; simp [boundaryCochain]; abel

lemma boundaryCochain_smul (c : ℂ) (Φ : Cusp → Binary ℂ) :
    boundaryCochain (c • Φ) = c • boundaryCochain Φ := by
  funext D; simp [boundaryCochain, smul_sub]

lemma reflection_sub (φ ψ : (Cusp × Cusp) → Binary ℂ) :
    reflection (φ - ψ) = reflection φ - reflection ψ := by
  funext D; simp [reflection]

lemma IsBoundaryDatum.sub {N n : ℕ} {Φ Ψ : Cusp → Binary ℂ} (hΦ : IsBoundaryDatum N n Φ)
    (hΨ : IsBoundaryDatum N n Ψ) : IsBoundaryDatum N n (Φ - Ψ) :=
  ⟨fun x => Submodule.sub_mem _ (hΦ.1 x) (hΨ.1 x),
    fun γ x => by simp only [Pi.sub_apply, hΦ.2 γ x, hΨ.2 γ x, map_sub]⟩

lemma IsBoundaryDatum.smul {N n : ℕ} (c : ℂ) {Φ : Cusp → Binary ℂ} (hΦ : IsBoundaryDatum N n Φ) :
    IsBoundaryDatum N n (c • Φ) :=
  ⟨fun x => Submodule.smul_mem _ c (hΦ.1 x),
    fun γ x => by simp only [Pi.smul_apply, hΦ.2 γ x, map_smul]⟩

end MTT.Cohomology

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ)
    (hI : ∀ f, IntegralClass f (I f))
    (g h : CuspForm (MTT.GammaOne N) (k : ℤ)) (Φ : Cusp → Binary ℂ)
    (hΦ : IsBoundaryDatum N (k-2) Φ) (e : ZMod N → ℂ)
    (hlaw : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      ((I g).val + reflection (I h).val + boundaryCochain Φ) (cuspAct γ.val x, cuspAct γ.val y) =
        e (γ.val 1 1 : ZMod N) •
          act γ.val.val (((I g).val + reflection (I h).val + boundaryCochain Φ) (x, y))) :
    (∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      (I g).val (cuspAct γ.val x, cuspAct γ.val y) =
        e (γ.val 1 1 : ZMod N) • act γ.val.val ((I g).val (x, y))) ∧
    (∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      reflection (I h).val (cuspAct γ.val x, cuspAct γ.val y) =
        e (γ.val 1 1 : ZMod N) • act γ.val.val (reflection (I h).val (x, y))) ∧
    (∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      boundaryCochain Φ (cuspAct γ.val x, cuspAct γ.val y) =
        e (γ.val 1 1 : ZMod N) • act γ.val.val (boundaryCochain Φ (x, y))) := by
  have key : ∀ γ : CongruenceSubgroup.Gamma0 N,
      (∀ x y, (I g).val (cuspAct γ.val x, cuspAct γ.val y) =
        e (γ.val 1 1 : ZMod N) • act γ.val.val ((I g).val (x, y))) ∧
      (∀ x y, reflection (I h).val (cuspAct γ.val x, cuspAct γ.val y) =
        e (γ.val 1 1 : ZMod N) • act γ.val.val (reflection (I h).val (x, y))) ∧
      (∀ x y, boundaryCochain Φ (cuspAct γ.val x, cuspAct γ.val y) =
        e (γ.val 1 1 : ZMod N) • act γ.val.val (boundaryCochain Φ (x, y))) := by
    intro γ
    obtain ⟨g', hg'⟩ := MTT.exists_cuspForm_slash_gamma0 hN g γ
    obtain ⟨h', hh'⟩ := MTT.exists_cuspForm_slash_gamma0 hN h (conjRefl γ)
    set c : ℂ := e (γ.val 1 1 : ZMod N) with hc
    -- the transported sum equals `c` times the sum
    have hsum' : (I g').val + reflection (I h').val + boundaryCochain (transportDatum γ Φ) =
        c • ((I g).val + reflection (I h).val + boundaryCochain Φ) := by
      funext D
      obtain ⟨x, y⟩ := D
      have hl := hlaw γ x y
      simp only [Pi.add_apply] at hl
      rw [transport_holo hN hk I hI g g' γ hg', transport_refl hN hk I hI h h' γ hh',
        boundaryCochain_transport γ Φ, ← map_add, ← map_add, ← map_smul] at hl
      have := act_injective_of_det_one γ.val.2 hl
      simpa only [Pi.add_apply, Pi.smul_apply, hc] using this
    have hdiff : (I (g' - c • g)).val + reflection (I (h' - c • h)).val +
        boundaryCochain (transportDatum γ Φ - c • Φ) = 0 := by
      calc (I (g' - c • g)).val + reflection (I (h' - c • h)).val +
            boundaryCochain (transportDatum γ Φ - c • Φ)
          = ((I g').val + reflection (I h').val + boundaryCochain (transportDatum γ Φ)) -
              c • ((I g).val + reflection (I h).val + boundaryCochain Φ) := by
            simp only [map_sub, map_smul, Submodule.coe_sub, Submodule.coe_smul, reflection_sub,
              reflection_smul, boundaryCochain_sub, boundaryCochain_smul, smul_add]
            abel
        _ = 0 := by rw [hsum', sub_self]
    obtain ⟨hg0, hh0, hΦ0⟩ := MTT.Cohomology.eichler_shimura_direct hN hk I hI (g' - c • g)
      (h' - c • h) (transportDatum γ Φ - c • Φ)
      ((transportDatum_isBoundaryDatum γ hΦ).sub (hΦ.smul c)) hdiff
    have hg'' : g' = c • g := sub_eq_zero.mp hg0
    have hh'' : h' = c • h := sub_eq_zero.mp hh0
    have hΦ'' : boundaryCochain (transportDatum γ Φ) = c • boundaryCochain Φ := by
      rw [boundaryCochain_sub, boundaryCochain_smul] at hΦ0
      exact sub_eq_zero.mp hΦ0
    refine ⟨fun x y => ?_, fun x y => ?_, fun x y => ?_⟩
    · rw [transport_holo hN hk I hI g g' γ hg', hg'', map_smul, Submodule.coe_smul, Pi.smul_apply,
        map_smul]
    · rw [transport_refl hN hk I hI h h' γ hh', hh'', map_smul, Submodule.coe_smul,
        reflection_smul, Pi.smul_apply, map_smul]
    · rw [boundaryCochain_transport γ Φ, hΦ'', Pi.smul_apply, map_smul]
  exact ⟨fun γ => (key γ).1, fun γ => (key γ).2.1, fun γ => (key γ).2.2⟩
