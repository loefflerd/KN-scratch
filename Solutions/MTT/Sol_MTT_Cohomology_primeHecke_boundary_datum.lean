import Definitions.MTT.Def_MTT_Cohomology_Boundary
import Definitions.MTT.Def_MTT_Cohomology_Integration
import Mathlib.Algebra.Field.ZMod
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
  rw [toGLQ, dite_eq_left (det_map_ne_zero h)]; rfl

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

/-! ### Part 1: the Hecke operator on boundary data -/

variable {N : ℕ}

/-- The prime Hecke operator on functions on cusps. -/
def heckeDatum (e : DirichletCharacter ℂ N) (l : ℕ) (Φ : Cusp → Binary ℂ) : Cusp → Binary ℂ :=
  fun x => ∑ b : Fin l, act (Matrix.adjugate !![1, (b.val : ℤ); 0, (l : ℤ)])
      (Φ (fractional !![1, (b.val : ℤ); 0, (l : ℤ)] x)) +
    e (l : ZMod N) • act (Matrix.adjugate !![(l : ℤ), 0; 0, 1]) (Φ (fractional !![(l : ℤ), 0; 0, 1] x))

lemma primeHecke_boundaryCochain (e : DirichletCharacter ℂ N) (l : ℕ) (Φ : Cusp → Binary ℂ) :
    primeHecke (e (l : ZMod N)) l (boundaryCochain Φ) = boundaryCochain (heckeDatum e l Φ) := by
  funext D
  simp only [primeHecke, slash, boundaryCochain, heckeDatum, Pi.add_apply, Finset.sum_apply,
    Pi.smul_apply, map_sub, Finset.sum_sub_distrib, smul_sub]
  abel

lemma heckeDatum_mem_Sym {n : ℕ} (e : DirichletCharacter ℂ N) (l : ℕ) {Φ : Cusp → Binary ℂ}
    (hΦ : ∀ x, Φ x ∈ Sym ℂ n) (x : Cusp) : heckeDatum e l Φ x ∈ Sym ℂ n := by
  unfold heckeDatum
  exact Submodule.add_mem _ (Submodule.sum_mem _ fun b _ => act_mem_Sym _ (hΦ _))
    (Submodule.smul_mem _ _ (act_mem_Sym _ (hΦ _)))

/-! ### Part 3: the coset permutation for boundary data -/

/-! ### The matrices `β_b = [1 b; 0 l]` and `α = [l 0; 0 1]` -/

variable (l : ℕ)

def β (b : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, (b : ℤ); 0, (l : ℤ)]
def α : Matrix (Fin 2) (Fin 2) ℤ := !![(l : ℤ), 0; 0, 1]

@[simp] lemma det_β (b : ℕ) : (β l b).det = l := by simp [β, Matrix.det_fin_two_of]
@[simp] lemma det_α : (α l).det = l := by simp [α, Matrix.det_fin_two_of]

/-- The coset representatives, indexed by `P¹(F_l) = F_l ∪ {∞}`. -/
def Mx : Option (ZMod l) → Matrix (Fin 2) (Fin 2) ℤ
  | none => α l
  | some b => β l b.val

@[simp] lemma Mx_none : Mx l none = α l := rfl
@[simp] lemma Mx_some (b : ZMod l) : Mx l (some b) = β l b.val := rfl

lemma det_Mx (x : Option (ZMod l)) : (Mx l x).det = l := by cases x <;> simp

/-- The coefficients: `1` on the `β_b`, `ε(l)` on `α`. -/
def cx (e : DirichletCharacter ℂ N) : Option (ZMod l) → ℂ
  | none => e l
  | some _ => 1

@[simp] lemma cx_none (e : DirichletCharacter ℂ N) : cx l e none = e l := rfl
@[simp] lemma cx_some (e : DirichletCharacter ℂ N) (b : ZMod l) : cx l e (some b) = 1 := rfl

variable {l} [hl : Fact l.Prime]

lemma det_Mx_pos (x : Option (ZMod l)) : 0 < (Mx l x).det := by
  rw [det_Mx]; exact_mod_cast hl.out.pos

lemma l_pos : 0 < (l : ℤ) := by exact_mod_cast hl.out.pos

/-! ### The Möbius permutation of `P¹(F_l)` -/

section moebius
variable {K : Type*} [Field K] [DecidableEq K]

/-- The action of `[A B; C D]` on `P¹(K) = K ∪ {∞}` by `t ↦ (B + tD)/(A + tC)`. -/
def mob (A B C D : K) : Option K → Option K
  | none => if C = 0 then none else some (D / C)
  | some t => if A + t * C = 0 then none else some ((B + t * D) / (A + t * C))

lemma mob_injective (A B C D : K) (h : A * D - B * C = 1) :
    Function.Injective (mob A B C D) := by
  intro x y hxy
  rcases x with _ | t <;> rcases y with _ | s
  · rfl
  · exfalso
    by_cases hC : C = 0
    · simp only [mob, ite_eq_left hC] at hxy
      split_ifs at hxy with hs
      all_goals first
        | exact Option.noConfusion hxy
        | (rw [hC, mul_zero, add_zero] at hs; rw [hs, hC] at h; simp at h)
    · by_cases hs : A + s * C = 0
      · simp [mob, hC, hs] at hxy
      · simp only [mob, ite_eq_right hC, ite_eq_right hs, Option.some.injEq] at hxy
        rw [div_eq_div_iff hC hs] at hxy
        have : A * D - B * C = 0 := by linear_combination hxy
        rw [h] at this; exact one_ne_zero this
  · exfalso
    by_cases hC : C = 0
    · simp only [mob, ite_eq_left hC] at hxy
      split_ifs at hxy with ht
      all_goals first
        | exact Option.noConfusion hxy
        | (rw [hC, mul_zero, add_zero] at ht; rw [ht, hC] at h; simp at h)
    · by_cases ht : A + t * C = 0
      · simp [mob, hC, ht] at hxy
      · simp only [mob, ite_eq_right hC, ite_eq_right ht, Option.some.injEq] at hxy
        rw [div_eq_div_iff ht hC] at hxy
        have : A * D - B * C = 0 := by linear_combination -hxy
        rw [h] at this; exact one_ne_zero this
  · by_cases ht : A + t * C = 0
    · by_cases hs : A + s * C = 0
      · by_cases hC : C = 0
        · exfalso; rw [hC, mul_zero, add_zero] at ht; rw [ht, hC] at h; simp at h
        · have : (t - s) * C = 0 := by linear_combination ht - hs
          rcases mul_eq_zero.mp this with h1 | h1
          · rw [sub_eq_zero.mp h1]
          · exact absurd h1 hC
      · exfalso; simp [mob, ht, hs] at hxy
    · by_cases hs : A + s * C = 0
      · exfalso; simp [mob, ht, hs] at hxy
      · simp only [mob, ite_eq_right ht, ite_eq_right hs, Option.some.injEq] at hxy
        rw [div_eq_div_iff ht hs] at hxy
        have : (t - s) * (A * D - B * C) = 0 := by linear_combination hxy
        rw [h, mul_one] at this
        rw [sub_eq_zero.mp this]

end moebius

section key
variable {l : ℕ} [hl : Fact l.Prime]

lemma det_entries (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := γ.2; rwa [Matrix.det_fin_two] at this

/-- The permutation of `P¹(F_l)` induced by `γ ∈ Γ₀(N)`. -/
def σγ (γ : Gamma0 N) : Option (ZMod l) → Option (ZMod l) :=
  mob ((γ.val 0 0 : ℤ) : ZMod l) ((γ.val 0 1 : ℤ) : ZMod l)
    ((γ.val 1 0 : ℤ) : ZMod l) ((γ.val 1 1 : ℤ) : ZMod l)

lemma σγ_injective (γ : Gamma0 N) : Function.Injective (σγ (l := l) γ) := by
  apply mob_injective
  have := congrArg (Int.cast : ℤ → ZMod l) (det_entries γ.val)
  push_cast at this
  exact this

/-- Build an element of `Γ₀(N)` from a matrix of determinant one. -/
def mkGamma0 (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = 1) (hc : (M 1 0 : ZMod N) = 0) :
    Gamma0 N :=
  ⟨⟨M, hdet⟩, Gamma0_mem.mpr hc⟩

@[simp] lemma mkGamma0_coe (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = 1)
    (hc : (M 1 0 : ZMod N) = 0) :
    ((mkGamma0 M hdet hc).val : Matrix (Fin 2) (Fin 2) ℤ) = M := rfl

lemma cast_val_eq (b : ZMod l) : ((b.val : ℤ) : ZMod l) = b := by
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

/-- `1` on the finite cosets, `l` on the coset at infinity. -/
def lpow (l : ℕ) : Option (ZMod l) → ℕ
  | none => l
  | some _ => 1

omit hl in
@[simp] lemma lpow_none : lpow l none = l := rfl
omit hl in
@[simp] lemma lpow_some (b : ZMod l) : lpow l (some b) = 1 := rfl

/-- The coset factorisation `M_x γ = γ' M_{σ x}`, with the residues of `γ'` mod `N`. -/
lemma key_factor (γ : Gamma0 N) (x : Option (ZMod l))
    (hgood : ¬ (x = none ∧ ((γ.val 1 0 : ℤ) : ZMod l) = 0 ∧ l ∣ N)) :
    ∃ γ' : Gamma0 N, Mx l x * (γ.val : Matrix (Fin 2) (Fin 2) ℤ) =
        (γ'.val : Matrix (Fin 2) (Fin 2) ℤ) * Mx l (σγ γ x) ∧
      ((lpow l (σγ γ x) : ℕ) : ZMod N) * ((γ'.val 0 0 : ℤ) : ZMod N) =
        ((lpow l x : ℕ) : ZMod N) * ((γ.val 0 0 : ℤ) : ZMod N) ∧
      ((lpow l x : ℕ) : ZMod N) * ((γ'.val 1 1 : ℤ) : ZMod N) =
        ((lpow l (σγ γ x) : ℕ) : ZMod N) * ((γ.val 1 1 : ℤ) : ZMod N) := by
  have hdet := det_entries γ.val
  have hcN : ((γ.val 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.mp γ.2
  rcases x with _ | b₀
  · -- the coset of `α = [l 0; 0 1]`
    by_cases hc0 : ((γ.val 1 0 : ℤ) : ZMod l) = 0
    · have hσ : σγ (l := l) γ none = none := by simp [σγ, mob, hc0]
      rw [hσ]
      by_cases hlN : l ∣ N
      · exact absurd ⟨rfl, hc0, hlN⟩ hgood
      · have hlc : (l : ℤ) ∣ γ.val 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ l).mp hc0
        have hcop : IsCoprime (N : ℤ) (l : ℤ) :=
          Nat.isCoprime_iff_coprime.mpr ((hl.out.coprime_iff_not_dvd.mpr hlN).symm)
        have hNc : (N : ℤ) ∣ γ.val 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hcN
        have hcl : (l : ℤ) * (γ.val 1 0 / l) = γ.val 1 0 := Int.mul_ediv_cancel' hlc
        have hNcl : (N : ℤ) ∣ γ.val 1 0 / l := by
          apply hcop.dvd_of_dvd_mul_left
          rw [hcl]; exact hNc
        let γ' : Gamma0 N := mkGamma0 !![γ.val 0 0, l * γ.val 0 1; γ.val 1 0 / l, γ.val 1 1]
          (by rw [Matrix.det_fin_two_of]; linear_combination hdet - γ.val 0 1 * hcl)
          (by simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr hNcl)
        refine ⟨γ', ?_, ?_, ?_⟩
        · ext i j
          fin_cases i <;> fin_cases j <;>
            simp [-ZMod.natCast_val, Mx, α, γ', mkGamma0, Matrix.mul_apply, Fin.sum_univ_two] <;>
            first | ring1 | linear_combination hcl | linear_combination -hcl
        · simp [γ', mkGamma0]
        · simp [γ', mkGamma0]
    · set b' : ZMod l := ((γ.val 1 1 : ℤ) : ZMod l) / ((γ.val 1 0 : ℤ) : ZMod l) with hb'
      have hσ : σγ (l := l) γ none = some b' := by simp [σγ, mob, hc0, hb']
      rw [hσ]
      have hdiv : (l : ℤ) ∣ γ.val 1 1 - γ.val 1 0 * b'.val := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val, hb']
        field_simp
        ring
      set d' : ℤ := (γ.val 1 1 - γ.val 1 0 * b'.val) / l with hd'
      have hld' : (l : ℤ) * d' = γ.val 1 1 - γ.val 1 0 * b'.val := Int.mul_ediv_cancel' hdiv
      let γ' : Gamma0 N :=
        mkGamma0 !![l * γ.val 0 0, γ.val 0 1 - γ.val 0 0 * b'.val; γ.val 1 0, d']
          (by rw [Matrix.det_fin_two_of]; linear_combination hdet + γ.val 0 0 * hld')
          (by simpa using hcN)
      refine ⟨γ', ?_, ?_, ?_⟩
      · ext i j
        fin_cases i <;> fin_cases j <;>
          simp [-ZMod.natCast_val, Mx, α, β, γ', mkGamma0, Matrix.mul_apply, Fin.sum_univ_two] <;>
          first | ring1 | linear_combination hld' | linear_combination -hld'
      · simp [γ', mkGamma0]
      · simp only [γ', mkGamma0_coe, lpow_none, lpow_some, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
          Nat.cast_one, one_mul]
        have := congrArg (Int.cast : ℤ → ZMod N) hld'
        push_cast at this
        rw [this, hcN]; ring
  · -- the coset of `β_{b₀} = [1 b₀; 0 l]`
    by_cases hu : ((γ.val 0 0 : ℤ) : ZMod l) + b₀ * ((γ.val 1 0 : ℤ) : ZMod l) = 0
    · have hσ : σγ (l := l) γ (some b₀) = none := by simp [σγ, mob, hu]
      rw [hσ]
      have hdiv : (l : ℤ) ∣ γ.val 0 0 + b₀.val * γ.val 1 0 := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [ZMod.natCast_zmod_val]; exact hu
      set u' : ℤ := (γ.val 0 0 + b₀.val * γ.val 1 0) / l with hu'
      have hlu : (l : ℤ) * u' = γ.val 0 0 + b₀.val * γ.val 1 0 := Int.mul_ediv_cancel' hdiv
      let γ' : Gamma0 N :=
        mkGamma0 !![u', γ.val 0 1 + b₀.val * γ.val 1 1; γ.val 1 0, l * γ.val 1 1]
          (by rw [Matrix.det_fin_two_of]; linear_combination hdet + γ.val 1 1 * hlu)
          (by simpa using hcN)
      refine ⟨γ', ?_, ?_, ?_⟩
      · ext i j
        fin_cases i <;> fin_cases j <;>
          simp [-ZMod.natCast_val, Mx, α, β, γ', mkGamma0, Matrix.mul_apply, Fin.sum_univ_two] <;>
          first | ring1 | linear_combination hlu | linear_combination -hlu
      · simp only [γ', mkGamma0_coe, lpow_none, lpow_some, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
          Nat.cast_one, one_mul]
        have := congrArg (Int.cast : ℤ → ZMod N) hlu
        push_cast at this
        rw [this, hcN]; ring
      · simp [γ', mkGamma0]
    · set b' : ZMod l := (((γ.val 0 1 : ℤ) : ZMod l) + b₀ * ((γ.val 1 1 : ℤ) : ZMod l)) /
          (((γ.val 0 0 : ℤ) : ZMod l) + b₀ * ((γ.val 1 0 : ℤ) : ZMod l)) with hb'
      have hσ : σγ (l := l) γ (some b₀) = some b' := by simp [σγ, mob, hu, hb']
      rw [hσ]
      have hdiv : (l : ℤ) ∣ (γ.val 0 1 + b₀.val * γ.val 1 1) -
          (γ.val 0 0 + b₀.val * γ.val 1 0) * b'.val := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        simp only [ZMod.natCast_zmod_val]
        rw [hb']
        field_simp
        ring
      set q : ℤ := ((γ.val 0 1 + b₀.val * γ.val 1 1) -
          (γ.val 0 0 + b₀.val * γ.val 1 0) * b'.val) / l with hq
      have hlq : (l : ℤ) * q = (γ.val 0 1 + b₀.val * γ.val 1 1) -
          (γ.val 0 0 + b₀.val * γ.val 1 0) * b'.val := Int.mul_ediv_cancel' hdiv
      let γ' : Gamma0 N :=
        mkGamma0 !![γ.val 0 0 + b₀.val * γ.val 1 0, q; l * γ.val 1 0, γ.val 1 1 - γ.val 1 0 * b'.val]
          (by rw [Matrix.det_fin_two_of]; linear_combination hdet - γ.val 1 0 * hlq)
          (by simp [hcN])
      refine ⟨γ', ?_, ?_, ?_⟩
      · ext i j
        fin_cases i <;> fin_cases j <;>
          simp [-ZMod.natCast_val, Mx, β, γ', mkGamma0, Matrix.mul_apply, Fin.sum_univ_two] <;>
          first | ring1 | linear_combination hlq | linear_combination -hlq
      · simp [γ', mkGamma0, hcN]
      · simp [γ', mkGamma0, hcN]

lemma det_Mx_ne {x : Option (ZMod l)} : (Mx l x).det ≠ 0 := (det_Mx_pos x).ne'

omit hl in
lemma cx_eq_lpow (e : DirichletCharacter ℂ N) (x : Option (ZMod l)) :
    cx l e x = e ((lpow l x : ℕ) : ZMod N) := by
  cases x <;> simp [cx, lpow]

/-- The character bookkeeping, derived from the residues. -/
lemma key_char (e : DirichletCharacter ℂ N) (γ γ' : Gamma0 N) (x : Option (ZMod l))
    (h11 : ((lpow l x : ℕ) : ZMod N) * ((γ'.val 1 1 : ℤ) : ZMod N) =
      ((lpow l (σγ γ x) : ℕ) : ZMod N) * ((γ.val 1 1 : ℤ) : ZMod N)) :
    cx l e x * e (γ'.val 1 1 : ZMod N) = e (γ.val 1 1 : ZMod N) * cx l e (σγ γ x) := by
  rw [cx_eq_lpow, cx_eq_lpow, ← map_mul, h11, map_mul, mul_comm]

/-- From `M_x γ = γ' M_y` (all of determinant `l` or `1`) deduce `adj(M_x) γ' = γ adj(M_y)`. -/
lemma adj_mul_of_factor (γ γ' : Gamma0 N) (x y : Option (ZMod l))
    (hfac : Mx l x * (γ.val : Matrix (Fin 2) (Fin 2) ℤ) =
      (γ'.val : Matrix (Fin 2) (Fin 2) ℤ) * Mx l y) :
    Matrix.adjugate (Mx l x) * (γ'.val : Matrix (Fin 2) (Fin 2) ℤ) =
      (γ.val : Matrix (Fin 2) (Fin 2) ℤ) * Matrix.adjugate (Mx l y) := by
  have h1 : Matrix.adjugate (Mx l x) * (γ'.val : Matrix (Fin 2) (Fin 2) ℤ) * Mx l y =
      (l : ℤ) • (γ.val : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [mul_assoc, ← hfac, ← mul_assoc, Matrix.adjugate_mul, det_Mx, smul_mul_assoc, one_mul]
  have h2 := congrArg (· * Matrix.adjugate (Mx l y)) h1
  simp only [smul_mul_assoc] at h2
  rw [mul_assoc, Matrix.mul_adjugate, det_Mx, mul_smul_comm, mul_one] at h2
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  exact smul_right_injective _ hl0 h2

/-- `Fin l ≃ ZMod l`, preserving `val`. -/
def finEquivZMod : Fin l ≃ ZMod l where
  toFun i := (i.val : ZMod l)
  invFun z := ⟨z.val, z.val_lt⟩
  left_inv i := by ext; simp [ZMod.val_natCast, Nat.mod_eq_of_lt i.2]
  right_inv z := by simp

lemma finEquivZMod_val (i : Fin l) : (finEquivZMod i : ZMod l).val = i.val := by
  simp [finEquivZMod, ZMod.val_natCast, Nat.mod_eq_of_lt i.2]

/-- The boundary Hecke operator written as a sum over `P¹(F_l)`. -/
lemma heckeDatum_eq_sum (e : DirichletCharacter ℂ N) (Φ : Cusp → Binary ℂ) (x : Cusp) :
    heckeDatum e l Φ x = ∑ z : Option (ZMod l),
      cx l e z • act (Matrix.adjugate (Mx l z)) (Φ (fractional (Mx l z) x)) := by
  rw [Fintype.sum_option]
  simp only [Mx_none, Mx_some, cx_none, cx_some, one_smul]
  unfold heckeDatum
  rw [add_comm]
  congr 1
  exact (Fintype.sum_equiv (finEquivZMod (l := l))
    (fun b : Fin l => act (Matrix.adjugate (β l b.val)) (Φ (fractional (β l b.val) x)))
    (fun z : ZMod l => act (Matrix.adjugate (β l z.val)) (Φ (fractional (β l z.val) x)))
    (fun b => by rw [finEquivZMod_val]))

/-- One term of the boundary Hecke operator, transported along `γ ∈ Γ₀(N)`. -/
lemma heckeDatum_term (e : DirichletCharacter ℂ N) (Φ : Cusp → Binary ℂ)
    (hlaw : ∀ γ : Gamma0 N, ∀ y : Cusp,
      Φ (cuspAct γ.val y) = e (γ.val 1 1 : ZMod N) • act γ.val.val (Φ y))
    (γ : Gamma0 N) (y : Cusp) (z : Option (ZMod l)) :
    cx l e z • act (Matrix.adjugate (Mx l z)) (Φ (fractional (Mx l z) (cuspAct γ.val y))) =
      e (γ.val 1 1 : ZMod N) • act γ.val.val
        (cx l e (σγ γ z) • act (Matrix.adjugate (Mx l (σγ γ z)))
          (Φ (fractional (Mx l (σγ γ z)) y))) := by
  have hγdet : ((γ.val : Matrix (Fin 2) (Fin 2) ℤ)).det ≠ 0 := by simp
  rw [← fractional_SL, ← fractional_mul det_Mx_ne hγdet]
  by_cases hgood : z = none ∧ ((γ.val 1 0 : ℤ) : ZMod l) = 0 ∧ l ∣ N
  · obtain ⟨rfl, hc0, hlN⟩ := hgood
    have h0 : e (l : ZMod N) = 0 := MulChar.map_nonunit e (by
      rw [ZMod.isUnit_iff_coprime]
      exact fun h => hl.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd h hlN))
    have hσ : σγ (l := l) γ none = none := by simp [σγ, mob, hc0]
    rw [hσ, cx_none, h0, zero_smul, zero_smul, map_zero, smul_zero]
  · obtain ⟨γ', hfac, -, h11⟩ := key_factor γ z hgood
    have hchar := key_char e γ γ' z h11
    have hγ'det : ((γ'.val : Matrix (Fin 2) (Fin 2) ℤ)).det ≠ 0 := by simp
    rw [hfac, fractional_mul hγ'det det_Mx_ne, fractional_SL, hlaw γ', map_smul, smul_smul,
      act_act, adj_mul_of_factor γ γ' z (σγ γ z) hfac, ← act_act, hchar, map_smul, smul_smul]

/-- The Γ₀(N)-law of the Hecke transform of a boundary datum with a genuine law. -/
theorem heckeDatum_law (e : DirichletCharacter ℂ N) (Φ : Cusp → Binary ℂ)
    (hlaw : ∀ γ : Gamma0 N, ∀ y : Cusp,
      Φ (cuspAct γ.val y) = e (γ.val 1 1 : ZMod N) • act γ.val.val (Φ y))
    (γ : Gamma0 N) (y : Cusp) :
    heckeDatum e l Φ (cuspAct γ.val y) =
      e (γ.val 1 1 : ZMod N) • act γ.val.val (heckeDatum e l Φ y) := by
  have hbij : Function.Bijective (σγ (l := l) γ) :=
    Finite.injective_iff_bijective.mp (σγ_injective γ)
  have h1 := Finset.sum_congr rfl (fun z (_ : z ∈ (Finset.univ : Finset (Option (ZMod l)))) =>
    heckeDatum_term e Φ hlaw γ y z)
  have h2 : ∑ z : Option (ZMod l), e (γ.val 1 1 : ZMod N) • act γ.val.val
        (cx l e (σγ γ z) • act (Matrix.adjugate (Mx l (σγ γ z)))
          (Φ (fractional (Mx l (σγ γ z)) y))) =
      ∑ z : Option (ZMod l), e (γ.val 1 1 : ZMod N) • act γ.val.val
        (cx l e z • act (Matrix.adjugate (Mx l z)) (Φ (fractional (Mx l z) y))) :=
    Fintype.sum_bijective (σγ γ) hbij _ _ (fun z => rfl)
  rw [heckeDatum_eq_sum, heckeDatum_eq_sum, map_sum, Finset.smul_sum, h1, h2]

end key

/-! ### Part 4: the representatives `β_b`, `σ_l α` and Γ₁(N)-factorisations -/

section sigma
variable {l : ℕ} [hl : Fact l.Prime]

/-- The inverse of `l` modulo `N`, as a natural number. -/
def linv (N l : ℕ) : ℕ := ((l : ZMod N)⁻¹).val

omit hl in
lemma linv_mul (hN : 0 < N) (hcop : Nat.Coprime l N) :
    ((linv N l : ℕ) : ZMod N) * (l : ZMod N) = 1 := by
  have : NeZero N := ⟨hN.ne'⟩
  rw [linv, ZMod.natCast_zmod_val, mul_comm]
  exact ZMod.mul_inv_of_unit _ ((ZMod.isUnit_iff_coprime l N).mpr hcop)

omit hl in
lemma N_dvd_linv_mul (hN : 0 < N) (hcop : Nat.Coprime l N) :
    (N : ℤ) ∣ (linv N l : ℤ) * l - 1 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [linv_mul hN hcop, sub_self]

/-- `σ_l ∈ Γ₀(N)` with `σ_l ≡ diag(l⁻¹, l)` modulo `N`. -/
def sigmaL (hN : 0 < N) (hcop : Nat.Coprime l N) : Gamma0 N :=
  mkGamma0 !![(linv N l : ℤ), ((linv N l : ℤ) * l - 1) / N; (N : ℤ), (l : ℤ)]
    (by
      rw [Matrix.det_fin_two_of]
      have := Int.mul_ediv_cancel' (N_dvd_linv_mul hN hcop)
      linear_combination -this)
    (by simp)

omit hl in
lemma sigmaL_00 (hN : 0 < N) (hcop : Nat.Coprime l N) :
    (sigmaL (l := l) hN hcop).val 0 0 = (linv N l : ℤ) := rfl
omit hl in
lemma sigmaL_10 (hN : 0 < N) (hcop : Nat.Coprime l N) :
    (sigmaL (l := l) hN hcop).val 1 0 = (N : ℤ) := rfl
omit hl in
lemma sigmaL_11 (hN : 0 < N) (hcop : Nat.Coprime l N) :
    (sigmaL (l := l) hN hcop).val 1 1 = (l : ℤ) := rfl

/-- The standard representatives: `β_b` on the finite cosets, `σ_l α` at infinity. -/
def Mstd (σ : Gamma0 N) : Option (ZMod l) → Matrix (Fin 2) (Fin 2) ℤ
  | none => (σ.val : Matrix (Fin 2) (Fin 2) ℤ) * α l
  | some b => β l b.val

omit hl in
@[simp] lemma Mstd_none (σ : Gamma0 N) : Mstd (l := l) σ none = (σ.val : Matrix (Fin 2) (Fin 2) ℤ) * α l := rfl
omit hl in
@[simp] lemma Mstd_some (σ : Gamma0 N) (b : ZMod l) : Mstd σ (some b) = β l b.val := rfl

omit hl in
lemma det_Mstd (σ : Gamma0 N) (x : Option (ZMod l)) : (Mstd σ x).det = l := by
  cases x <;> simp [Matrix.det_mul]

lemma det_Mstd_ne (σ : Gamma0 N) {x : Option (ZMod l)} : (Mstd σ x).det ≠ 0 := by
  rw [det_Mstd]; exact_mod_cast hl.out.ne_zero

/-- From `M_x δ = γ' M_y` (both of determinant `l`) deduce `adj(M_x) γ' = δ adj(M_y)`. -/
lemma adj_mul_of_factor' (δ γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (Mx' My' : Matrix (Fin 2) (Fin 2) ℤ) (hx : Mx'.det = l) (hy : My'.det = l)
    (hfac : Mx' * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * My') :
    Matrix.adjugate Mx' * (γ' : Matrix (Fin 2) (Fin 2) ℤ) =
      (δ : Matrix (Fin 2) (Fin 2) ℤ) * Matrix.adjugate My' := by
  have h1 : Matrix.adjugate Mx' * (γ' : Matrix (Fin 2) (Fin 2) ℤ) * My' =
      (l : ℤ) • (δ : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [mul_assoc, ← hfac, ← mul_assoc, Matrix.adjugate_mul, hx, smul_mul_assoc, one_mul]
  have h2 := congrArg (· * Matrix.adjugate My') h1
  simp only [smul_mul_assoc] at h2
  rw [mul_assoc, Matrix.mul_adjugate, hy, mul_smul_comm, mul_one] at h2
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  exact smul_right_injective _ hl0 h2

lemma Gamma1_of_residues {γ : Gamma0 N} (h00 : ((γ.val 0 0 : ℤ) : ZMod N) = 1)
    (h11 : ((γ.val 1 1 : ℤ) : ZMod N) = 1) : γ.val ∈ Gamma1 N := by
  rw [Gamma1_mem]
  exact ⟨h00, h11, Gamma0_mem.mp γ.2⟩

omit hl in
lemma sigmaL_coe (hN : 0 < N) (hcop : Nat.Coprime l N) :
    ((sigmaL (l := l) hN hcop).val : Matrix (Fin 2) (Fin 2) ℤ) =
      !![(linv N l : ℤ), ((linv N l : ℤ) * l - 1) / N; (N : ℤ), (l : ℤ)] := rfl

omit hl in
lemma adjugate_sigmaL (hN : 0 < N) (hcop : Nat.Coprime l N) :
    Matrix.adjugate ((sigmaL (l := l) hN hcop).val : Matrix (Fin 2) (Fin 2) ℤ) =
      !![(l : ℤ), -(((linv N l : ℤ) * l - 1) / N); -(N : ℤ), (linv N l : ℤ)] := by
  rw [sigmaL_coe, Matrix.adjugate_fin_two_of]

/-- `Γ₁(N)` is normal in `Γ₀(N)`. -/
lemma conj_mem_Gamma1 (γ : Gamma0 N) {δ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hδ : δ ∈ Gamma1 N) : γ.val * δ * γ.val⁻¹ ∈ Gamma1 N := by
  rw [Gamma1, Subgroup.mem_map] at hδ ⊢
  obtain ⟨δ', -, rfl⟩ := hδ
  refine ⟨⟨γ * δ'.val * γ⁻¹, ?_⟩, Subgroup.mem_top _, ?_⟩
  · exact (MonoidHom.normal_ker (Gamma0Map N)).conj_mem δ'.val δ'.property γ
  · simp

/-- The Γ₁(N)-factorisation for the standard representatives (`l ∤ N`). -/
lemma key_std (hN : 0 < N) (hcop : Nat.Coprime l N) (δ : Gamma1 N) (x : Option (ZMod l)) :
    ∃ γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ' ∈ Gamma1 N ∧
      Mstd (sigmaL (l := l) hN hcop) x * (δ.val : Matrix (Fin 2) (Fin 2) ℤ) =
        (γ' : Matrix (Fin 2) (Fin 2) ℤ) *
          Mstd (sigmaL (l := l) hN hcop) (σγ ⟨δ.val, Gamma1_in_Gamma0 N δ.2⟩ x) := by
  obtain ⟨ha, hd, hc⟩ := (Gamma1_mem N δ.val).mp δ.2
  have hlN : ¬ l ∣ N := (hl.out.coprime_iff_not_dvd).mp hcop
  have hgood : ¬ (x = none ∧ (((⟨δ.val, Gamma1_in_Gamma0 N δ.2⟩ : Gamma0 N).val 1 0 : ℤ) : ZMod l) = 0 ∧
      l ∣ N) := fun h => hlN h.2.2
  obtain ⟨γ₀, hfac, h00, h11⟩ := key_factor ⟨δ.val, Gamma1_in_Gamma0 N δ.2⟩ x hgood
  have hu := linv_mul hN hcop
  have hγ₀c : ((γ₀.val 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.mp γ₀.2
  have hσdet : ((sigmaL (l := l) hN hcop).val : Matrix (Fin 2) (Fin 2) ℤ).det = 1 :=
    (sigmaL (l := l) hN hcop).val.2
  have hNz : (N : ZMod N) = 0 := ZMod.natCast_self N
  rcases x with _ | b₀
  · rcases hσx : σγ (⟨δ.val, Gamma1_in_Gamma0 N δ.2⟩ : Gamma0 N) (none : Option (ZMod l))
      with _ | b'
    · -- ∞ ↦ ∞ : conjugate `γ₀` by `σ_l`
      rw [hσx] at hfac h00 h11
      simp only [lpow_none, Mx_none] at hfac h00 h11
      have hγ₀1 : γ₀.val ∈ Gamma1 N := Gamma1_of_residues
        (by
          have : ((linv N l : ℕ) : ZMod N) * ((l : ZMod N) * ((γ₀.val 0 0 : ℤ) : ZMod N)) =
              ((linv N l : ℕ) : ZMod N) * ((l : ZMod N) * ((δ.val 0 0 : ℤ) : ZMod N)) := by
            rw [h00]
          rwa [← mul_assoc, hu, one_mul, ← mul_assoc, hu, one_mul, ha] at this)
        (by
          have : ((linv N l : ℕ) : ZMod N) * ((l : ZMod N) * ((γ₀.val 1 1 : ℤ) : ZMod N)) =
              ((linv N l : ℕ) : ZMod N) * ((l : ZMod N) * ((δ.val 1 1 : ℤ) : ZMod N)) := by
            rw [h11]
          rwa [← mul_assoc, hu, one_mul, ← mul_assoc, hu, one_mul, hd] at this)
      refine ⟨(sigmaL (l := l) hN hcop).val * γ₀.val * (sigmaL (l := l) hN hcop).val⁻¹,
        conj_mem_Gamma1 _ hγ₀1, ?_⟩
      simp only [Mstd_none]
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_inv]
      calc ((sigmaL (l := l) hN hcop).val : Matrix (Fin 2) (Fin 2) ℤ) * α l *
            (δ.val : Matrix (Fin 2) (Fin 2) ℤ)
          = ((sigmaL (l := l) hN hcop).val : Matrix (Fin 2) (Fin 2) ℤ) *
              (γ₀.val * α l) := by rw [mul_assoc, hfac]
        _ = _ := by
          rw [mul_assoc (_ * _) (Matrix.adjugate _), ← mul_assoc (Matrix.adjugate _),
            Matrix.adjugate_mul, hσdet, one_smul, one_mul, mul_assoc]
    · -- ∞ ↦ b' : `γ' = σ_l γ₀`
      rw [hσx] at hfac h00 h11
      simp only [lpow_none, lpow_some, Mx_none, Mx_some, Nat.cast_one, one_mul] at hfac h00 h11
      refine ⟨(sigmaL (l := l) hN hcop).val * γ₀.val, Gamma1_of_residues (γ := ⟨_, mul_mem
        (sigmaL (l := l) hN hcop).2 γ₀.2⟩) ?_ ?_, ?_⟩
      · change (((((sigmaL (l := l) hN hcop).val : Matrix (Fin 2) (Fin 2) ℤ) * γ₀.val) 0 0 : ℤ) :
          ZMod N) = 1
        rw [sigmaL_coe]
        simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
        push_cast
        rw [hγ₀c, mul_zero, add_zero, h00, ha, mul_one, hu]
      · change (((((sigmaL (l := l) hN hcop).val : Matrix (Fin 2) (Fin 2) ℤ) * γ₀.val) 1 1 : ℤ) :
          ZMod N) = 1
        rw [sigmaL_coe]
        simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
        push_cast
        rw [hNz, zero_mul, zero_add, h11, hd]
      · simp only [Mstd_none, Mstd_some]
        rw [Matrix.SpecialLinearGroup.coe_mul, mul_assoc, hfac, mul_assoc]
  · rcases hσx : σγ (⟨δ.val, Gamma1_in_Gamma0 N δ.2⟩ : Gamma0 N) (some b₀) with _ | b''
    · -- b₀ ↦ ∞ : `γ' = γ₀ σ_l⁻¹`
      rw [hσx] at hfac h00 h11
      simp only [lpow_none, lpow_some, Mx_none, Mx_some, Nat.cast_one, one_mul] at hfac h00 h11
      refine ⟨γ₀.val * (sigmaL (l := l) hN hcop).val⁻¹, Gamma1_of_residues (γ := ⟨_, mul_mem
        γ₀.2 (inv_mem (sigmaL (l := l) hN hcop).2)⟩) ?_ ?_, ?_⟩
      · change ((((γ₀.val : Matrix (Fin 2) (Fin 2) ℤ) *
          ((sigmaL (l := l) hN hcop).val⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ)) 0 0 : ℤ) :
          ZMod N) = 1
        rw [Matrix.SpecialLinearGroup.coe_inv, adjugate_sigmaL]
        simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
        push_cast
        rw [hNz, neg_zero, mul_zero, add_zero, mul_comm, h00, ha]
      · change ((((γ₀.val : Matrix (Fin 2) (Fin 2) ℤ) *
          ((sigmaL (l := l) hN hcop).val⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ)) 1 1 : ℤ) :
          ZMod N) = 1
        rw [Matrix.SpecialLinearGroup.coe_inv, adjugate_sigmaL]
        simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
        push_cast
        rw [hγ₀c, zero_mul, zero_add, h11, hd, mul_one, mul_comm, hu]
      · simp only [Mstd_none, Mstd_some]
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, hfac,
          mul_assoc, ← mul_assoc (Matrix.adjugate _), Matrix.adjugate_mul, hσdet, one_smul,
          one_mul]
    · -- b₀ ↦ b'' : `γ' = γ₀`
      rw [hσx] at hfac h00 h11
      simp only [lpow_some, Mx_some, Nat.cast_one, one_mul] at hfac h00 h11
      refine ⟨γ₀.val, Gamma1_of_residues (by rw [h00, ha]) (by rw [h11, hd]), ?_⟩
      simpa only [Mstd_some] using hfac

end sigma

/-! ### Part 5: the standard Hecke transform and the main theorem -/

section std
variable {l : ℕ} [hl : Fact l.Prime]

/-- The standard Hecke transform of a function on cusps, for `l ∤ N`. -/
def heckeStd (σ : Gamma0 N) (Φ : Cusp → Binary ℂ) : Cusp → Binary ℂ :=
  fun x => ∑ z : Option (ZMod l),
    act (Matrix.adjugate (Mstd σ z)) (Φ (fractional (Mstd σ z) x))

lemma heckeStd_mem_Sym {n : ℕ} (σ : Gamma0 N) {Φ : Cusp → Binary ℂ} (hΦ : ∀ x, Φ x ∈ Sym ℂ n)
    (x : Cusp) : heckeStd (l := l) σ Φ x ∈ Sym ℂ n :=
  Submodule.sum_mem _ fun _z _ => act_mem_Sym _ (hΦ _)

lemma heckeStd_term (hN : 0 < N) (hcop : Nat.Coprime l N) (Φ : Cusp → Binary ℂ)
    (hΦ : ∀ δ : Gamma1 N, ∀ y, Φ (cuspAct δ.val y) = act δ.val.val (Φ y))
    (δ : Gamma1 N) (y : Cusp) (z : Option (ZMod l)) :
    act (Matrix.adjugate (Mstd (sigmaL (l := l) hN hcop) z))
        (Φ (fractional (Mstd (sigmaL (l := l) hN hcop) z) (cuspAct δ.val y))) =
      act δ.val.val (act (Matrix.adjugate (Mstd (sigmaL (l := l) hN hcop)
          (σγ ⟨δ.val, Gamma1_in_Gamma0 N δ.2⟩ z)))
        (Φ (fractional (Mstd (sigmaL (l := l) hN hcop) (σγ ⟨δ.val, Gamma1_in_Gamma0 N δ.2⟩ z)) y))) := by
  obtain ⟨γ', hγ', hfac⟩ := key_std hN hcop δ z
  have hδdet : ((δ.val : Matrix (Fin 2) (Fin 2) ℤ)).det ≠ 0 := by simp
  have hγ'det : ((γ' : Matrix (Fin 2) (Fin 2) ℤ)).det ≠ 0 := by simp
  have hΦ' := hΦ ⟨γ', hγ'⟩ (fractional (Mstd (sigmaL (l := l) hN hcop)
    (σγ ⟨δ.val, Gamma1_in_Gamma0 N δ.2⟩ z)) y)
  simp only at hΦ'
  rw [← fractional_SL, ← fractional_mul (det_Mstd_ne _) hδdet, hfac,
    fractional_mul hγ'det (det_Mstd_ne _), fractional_SL, hΦ', act_act,
    adj_mul_of_factor' δ.val γ' _ _ (det_Mstd _ _) (det_Mstd _ _) hfac, ← act_act]

theorem heckeStd_equivariant (hN : 0 < N) (hcop : Nat.Coprime l N) (Φ : Cusp → Binary ℂ)
    (hΦ : ∀ δ : Gamma1 N, ∀ y, Φ (cuspAct δ.val y) = act δ.val.val (Φ y))
    (δ : Gamma1 N) (y : Cusp) :
    heckeStd (l := l) (sigmaL (l := l) hN hcop) Φ (cuspAct δ.val y) =
      act δ.val.val (heckeStd (l := l) (sigmaL (l := l) hN hcop) Φ y) := by
  unfold heckeStd
  rw [map_sum]
  have hbij : Function.Bijective (σγ (l := l) ⟨δ.val, Gamma1_in_Gamma0 N δ.2⟩) :=
    Finite.injective_iff_bijective.mp (σγ_injective _)
  rw [Finset.sum_congr rfl (fun z (_ : z ∈ (Finset.univ : Finset (Option (ZMod l)))) =>
    heckeStd_term hN hcop Φ hΦ δ y z)]
  exact Fintype.sum_bijective _ hbij _ _ (fun z => rfl)

/-- The defect of the nebentype law of `Φ` at `γ` is independent of the point. -/
lemma defect_const (e : DirichletCharacter ℂ N) {Φ : Cusp → Binary ℂ}
    (hlaw : ∀ γ : Gamma0 N, ∀ x y,
      boundaryCochain Φ (cuspAct γ.val x, cuspAct γ.val y) =
        e (γ.val 1 1 : ZMod N) • act γ.val.val (boundaryCochain Φ (x, y)))
    (γ : Gamma0 N) (x y : Cusp) :
    Φ (cuspAct γ.val y) - e (γ.val 1 1 : ZMod N) • act γ.val.val (Φ y) =
      Φ (cuspAct γ.val x) - e (γ.val 1 1 : ZMod N) • act γ.val.val (Φ x) := by
  have h := hlaw γ x y
  simp only [boundaryCochain, map_sub, smul_sub] at h
  calc Φ (cuspAct γ.val y) - e (γ.val 1 1 : ZMod N) • act γ.val.val (Φ y)
      = (Φ (cuspAct γ.val y) - Φ (cuspAct γ.val x)) -
          (e (γ.val 1 1 : ZMod N) • act γ.val.val (Φ y) -
            e (γ.val 1 1 : ZMod N) • act γ.val.val (Φ x)) +
          (Φ (cuspAct γ.val x) - e (γ.val 1 1 : ZMod N) • act γ.val.val (Φ x)) := by abel
    _ = _ := by rw [h]; abel

omit hl in
lemma matrix_eq_β (b : ℕ) : (!![1, (b : ℤ); 0, (l : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) = β l b := rfl
omit hl in
lemma matrix_eq_α : (!![(l : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) = α l := rfl

/-- The standard and the platform Hecke transforms differ by a constant. -/
lemma heckeStd_sub_heckeDatum (hN : 0 < N) (hcop : Nat.Coprime l N) (e : DirichletCharacter ℂ N)
    (Φ : Cusp → Binary ℂ)
    (hlaw : ∀ γ : Gamma0 N, ∀ x y,
      boundaryCochain Φ (cuspAct γ.val x, cuspAct γ.val y) =
        e (γ.val 1 1 : ZMod N) • act γ.val.val (boundaryCochain Φ (x, y))) :
    ∃ K : Binary ℂ, ∀ x, heckeStd (l := l) (sigmaL (l := l) hN hcop) Φ x = heckeDatum e l Φ x + K := by
  set σ := sigmaL (l := l) hN hcop with hσ
  have hσ11 : ((σ.val 1 1 : ℤ) : ZMod N) = (l : ZMod N) := by
    rw [hσ, sigmaL_11]; simp
  have hσdet : ((σ.val : Matrix (Fin 2) (Fin 2) ℤ)).det = 1 := σ.val.2
  set c : Binary ℂ := Φ (cuspAct σ.val OnePoint.infty) -
    e (l : ZMod N) • act σ.val.val (Φ OnePoint.infty) with hc
  have hdef : ∀ z, Φ (cuspAct σ.val z) = e (l : ZMod N) • act σ.val.val (Φ z) + c := by
    intro z
    have := defect_const e hlaw σ OnePoint.infty z
    rw [hσ11] at this
    rw [hc, ← this]; abel
  refine ⟨act (Matrix.adjugate (α l)) (act (Matrix.adjugate σ.val.val) c), fun x => ?_⟩
  have hα : (α l).det ≠ 0 := by rw [det_α]; exact_mod_cast hl.out.ne_zero
  have hinf : act (Matrix.adjugate (σ.val.val * α l)) (Φ (fractional (σ.val.val * α l) x)) =
      e (l : ZMod N) • act (Matrix.adjugate (α l)) (Φ (fractional (α l) x)) +
        act (Matrix.adjugate (α l)) (act (Matrix.adjugate σ.val.val) c) := by
    rw [fractional_mul (by simp) hα, fractional_SL, hdef, Matrix.adjugate_mul_distrib, ← act_act,
      map_add, map_smul, act_act, Matrix.adjugate_mul, hσdet, one_smul, act_one, map_add, map_smul]
  unfold heckeStd heckeDatum
  simp only [matrix_eq_β, matrix_eq_α]
  rw [Fintype.sum_option]
  simp only [Mstd_none, Mstd_some]
  rw [hinf]
  have hfin : ∑ z : ZMod l, act (Matrix.adjugate (β l z.val)) (Φ (fractional (β l z.val) x)) =
      ∑ b : Fin l, act (Matrix.adjugate (β l b.val)) (Φ (fractional (β l b.val) x)) :=
    (Fintype.sum_equiv (finEquivZMod (l := l))
      (fun b : Fin l => act (Matrix.adjugate (β l b.val)) (Φ (fractional (β l b.val) x)))
      (fun z : ZMod l => act (Matrix.adjugate (β l z.val)) (Φ (fractional (β l z.val) x)))
      (fun b => by rw [finEquivZMod_val])).symm
  rw [hfin]
  abel

/-- For `l ∣ N` the platform Hecke transform is itself Γ₁(N)-equivariant. -/
theorem heckeDatum_equivariant_of_dvd (_hN : 0 < N) (hlN : l ∣ N) (e : DirichletCharacter ℂ N)
    (Φ : Cusp → Binary ℂ)
    (hΦ : ∀ δ : Gamma1 N, ∀ y, Φ (cuspAct δ.val y) = act δ.val.val (Φ y))
    (δ : Gamma1 N) (y : Cusp) :
    heckeDatum e l Φ (cuspAct δ.val y) = act δ.val.val (heckeDatum e l Φ y) := by
  set δ₀ : Gamma0 N := ⟨δ.val, Gamma1_in_Gamma0 N δ.2⟩ with hδ₀
  obtain ⟨ha, hd, hc⟩ := (Gamma1_mem N δ.val).mp δ.2
  have hlN' : (l : ℤ) ∣ N := Int.natCast_dvd_natCast.mpr hlN
  have hmodl : ∀ z : ℤ, ((z : ZMod N) = 1 → (z : ZMod l) = 1) ∧ ((z : ZMod N) = 0 → (z : ZMod l) = 0) := by
    intro z
    constructor
    · intro h
      have h' : (N : ℤ) ∣ z - 1 := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h, sub_self]
      have := dvd_trans hlN' h'
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at this
      push_cast at this
      exact sub_eq_zero.mp this
    · intro h
      have h' : (N : ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd z N).mp h
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd z l).mpr (dvd_trans hlN' h')
  have hal : ((δ.val 0 0 : ℤ) : ZMod l) = 1 := (hmodl _).1 ha
  have hcl : ((δ.val 1 0 : ℤ) : ZMod l) = 0 := (hmodl _).2 hc
  have h0 : e (l : ZMod N) = 0 := MulChar.map_nonunit e (by
    rw [ZMod.isUnit_iff_coprime]
    exact fun h => hl.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd h hlN))
  have hδdet : ((δ.val : Matrix (Fin 2) (Fin 2) ℤ)).det ≠ 0 := by simp
  rw [heckeDatum_eq_sum, heckeDatum_eq_sum, map_sum]
  have hbij : Function.Bijective (σγ (l := l) δ₀) :=
    Finite.injective_iff_bijective.mp (σγ_injective _)
  have hterm : ∀ z : Option (ZMod l),
      cx l e z • act (Matrix.adjugate (Mx l z)) (Φ (fractional (Mx l z) (cuspAct δ.val y))) =
        act δ.val.val (cx l e (σγ δ₀ z) • act (Matrix.adjugate (Mx l (σγ δ₀ z)))
          (Φ (fractional (Mx l (σγ δ₀ z)) y))) := by
    intro z
    rcases z with _ | b₀
    · have hσ : σγ (l := l) δ₀ none = none := by simp [σγ, mob, hδ₀, hcl]
      rw [hσ, cx_none, h0, zero_smul, zero_smul, map_zero]
    · have hgood : ¬ (some b₀ = none ∧ ((δ₀.val 1 0 : ℤ) : ZMod l) = 0 ∧ l ∣ N) :=
        fun h => Option.some_ne_none b₀ h.1
      obtain ⟨γ₀, hfac, h00, h11⟩ := key_factor δ₀ (some b₀) hgood
      have hu : ((δ.val 0 0 : ℤ) : ZMod l) + b₀ * ((δ.val 1 0 : ℤ) : ZMod l) ≠ 0 := by
        rw [hal, hcl, mul_zero, add_zero]; exact one_ne_zero
      have hσ : ∃ b', σγ (l := l) δ₀ (some b₀) = some b' :=
        ⟨(((δ.val 0 1 : ℤ) : ZMod l) + b₀ * ((δ.val 1 1 : ℤ) : ZMod l)) /
          (((δ.val 0 0 : ℤ) : ZMod l) + b₀ * ((δ.val 1 0 : ℤ) : ZMod l)),
          by simp [σγ, mob, hδ₀, hu]⟩
      obtain ⟨b', hb'⟩ := hσ
      rw [hb'] at hfac h00 h11 ⊢
      simp only [lpow_some, Nat.cast_one, one_mul] at h00 h11
      have hγ₀1 : γ₀.val ∈ Gamma1 N := Gamma1_of_residues (by rw [h00]; exact ha)
        (by rw [h11]; exact hd)
      have hγ₀det : ((γ₀.val : Matrix (Fin 2) (Fin 2) ℤ)).det ≠ 0 := by simp
      have hΦ' := hΦ ⟨γ₀.val, hγ₀1⟩ (fractional (Mx l (some b')) y)
      simp only at hΦ'
      rw [cx_some, cx_some, one_smul, one_smul, ← fractional_SL, ← fractional_mul det_Mx_ne hδdet, hfac,
        fractional_mul hγ₀det det_Mx_ne, fractional_SL, hΦ', act_act,
        adj_mul_of_factor δ₀ γ₀ (some b₀) (some b') hfac, ← act_act]
  rw [Finset.sum_congr rfl (fun z (_ : z ∈ (Finset.univ : Finset (Option (ZMod l)))) => hterm z)]
  exact Fintype.sum_bijective _ hbij _ _ (fun z => rfl)

end std

/-- **Hecke operators preserve boundary classes with a nebentype law.** -/
theorem primeHecke_boundary_datum_proof
    {N k : ℕ} (hN : 0 < N) (_hk : 2 ≤ k) (e : DirichletCharacter ℂ N)
    (Φ : Cusp → Binary ℂ) (hΦ : IsBoundaryDatum N (k-2) Φ)
    (hlaw : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      boundaryCochain Φ (cuspAct γ.val x, cuspAct γ.val y) =
        e (γ.val 1 1 : ZMod N) • act γ.val.val (boundaryCochain Φ (x, y)))
    (l : ℕ) (hl : l.Prime) :
    ∃ Ψ : Cusp → Binary ℂ, IsBoundaryDatum N (k-2) Ψ ∧
      primeHecke (e (l : ZMod N)) l (boundaryCochain Φ) = boundaryCochain Ψ := by
  have : Fact l.Prime := ⟨hl⟩
  by_cases hlN : l ∣ N
  · exact ⟨heckeDatum e l Φ, ⟨heckeDatum_mem_Sym e l hΦ.1,
      fun δ x => heckeDatum_equivariant_of_dvd hN hlN e Φ hΦ.2 δ x⟩,
      primeHecke_boundaryCochain e l Φ⟩
  · have hcop : Nat.Coprime l N := (hl.coprime_iff_not_dvd).mpr hlN
    refine ⟨heckeStd (l := l) (sigmaL (l := l) hN hcop) Φ, ⟨heckeStd_mem_Sym _ hΦ.1,
      fun δ x => heckeStd_equivariant hN hcop Φ hΦ.2 δ x⟩, ?_⟩
    rw [primeHecke_boundaryCochain]
    obtain ⟨K, hK⟩ := heckeStd_sub_heckeDatum hN hcop e Φ hlaw
    funext D
    simp only [boundaryCochain, hK]
    abel

end MTT.Cohomology

open MTT.Cohomology

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (e : DirichletCharacter ℂ N)
    (Φ : Cusp → Binary ℂ) (hΦ : IsBoundaryDatum N (k-2) Φ)
    (hlaw : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      boundaryCochain Φ (cuspAct γ.val x, cuspAct γ.val y) =
        e (γ.val 1 1 : ZMod N) • act γ.val.val (boundaryCochain Φ (x, y)))
    (l : ℕ) (hl : l.Prime) :
    ∃ Ψ : Cusp → Binary ℂ, IsBoundaryDatum N (k-2) Ψ ∧
      primeHecke (e (l : ZMod N)) l (boundaryCochain Φ) = boundaryCochain Ψ :=
  MTT.Cohomology.primeHecke_boundary_datum_proof hN hk e Φ hΦ hlaw l hl
