import Theorems.MTT.Thm_MTT_exists_cuspForm_slash_gamma0
import Theorems.MTT.Thm_MTT_Cohomology_cuspPrimitive_slash_relation
import Theorems.MTT.Thm_MTT_period_vanishing
import Theorems.MTT.Thm_MTT_Cohomology_evaluation_faithful
import Definitions.MTT.Def_MTT_Cohomology_Integration
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

/-- Any integration map is injective (from `period_vanishing`). -/
theorem injective_of_integralClass {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ)
    (hI : ∀ f, IntegralClass f (I f)) : Function.Injective I := by
  intro f g hfg
  have h0 : I (f - g) = 0 := by rw [map_sub, hfg, sub_self]
  have hcls := hI (f - g)
  rw [h0] at hcls
  have hzero : f - g = 0 := MTT.period_vanishing hN hk (f - g) (fun j hj r => by
    have h := hcls j r hj
    rw [map_zero] at h
    have hch : (((k-2).choose j : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj).ne'
    exact (mul_eq_zero.mp h.symm).resolve_left hch)
  exact sub_eq_zero.mp hzero

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

end MTT.Cohomology

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ)
    (hI : ∀ f, IntegralClass f (I f))
    (e : ZMod N → ℂ) (g : CuspForm (MTT.GammaOne N) (k : ℤ))
    (hlaw : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      (I g).val (cuspAct γ.val x, cuspAct γ.val y) =
        e (γ.val 1 1 : ZMod N) • act γ.val.val ((I g).val (x, y))) :
    ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane,
      g ((Matrix.SpecialLinearGroup.mapGL ℝ γ.val) • z) =
        e (γ.val 1 1 : ZMod N) *
          (((γ.val 1 0 : ℤ) : ℂ) * z + ((γ.val 1 1 : ℤ) : ℂ)) ^ k * g z := by
  intro γ z
  obtain ⟨g', hg'⟩ := MTT.exists_cuspForm_slash_gamma0 hN g γ
  have hinj := injective_of_integralClass hN hk I hI
  obtain ⟨hsym, hcocy, -⟩ := (I g).2
  -- the class of `g` at `(∞, s)` is the cusp primitive
  have hval : ∀ s : Cusp, (I g).val (OnePoint.infty, s) = cuspPrimitive g s := by
    intro s
    rcases s with _ | r
    · have hc := hcocy OnePoint.infty OnePoint.infty OnePoint.infty
      exact add_eq_left.mp hc
    · apply Sym_ext (hsym _ _) (cuspPeriodPolynomial_mem_Sym hk g r)
      intro j hj
      change evaluation j r (I g) = _
      rw [hI g j r hj, coeff_cuspPeriodPolynomial hk g r hj]
  have hcoc : ∀ x y : Cusp, (I g).val (x, y) =
      (I g).val (OnePoint.infty, y) - (I g).val (OnePoint.infty, x) := by
    intro x y
    have := hcocy OnePoint.infty x y
    rw [← this]; abel
  -- the period polynomial of `g|γ` is `e(d)` times that of `g`
  have hpoly : ∀ r : ℚ, cuspPeriodPolynomial g' r =
      e (γ.val 1 1 : ZMod N) • cuspPeriodPolynomial g r := by
    intro r
    have hE := MTT.Cohomology.cuspPrimitive_slash_relation hN hk g g' γ hg' (r : Cusp)
    have hL := hlaw γ OnePoint.infty (r : Cusp)
    rw [hcoc] at hL
    simp only [hval] at hL
    have h1 : act γ.val.val (cuspPrimitive g' (r : Cusp)) =
        act γ.val.val (e (γ.val 1 1 : ZMod N) • cuspPrimitive g (r : Cusp)) := by
      rw [map_smul, ← hL, hE]; abel
    exact act_injective_of_det_one γ.val.2 h1
  -- hence `I g' = e(d) • I g`
  have hIg' : I g' = e (γ.val 1 1 : ZMod N) • I g := by
    apply MTT.Cohomology.evaluation_faithful
    intro j r hj
    rw [map_smul, smul_eq_mul, hI g' j r hj, hI g j r hj]
    have := congrArg (MvPolynomial.coeff (binaryExponent (k - 2) j)) (hpoly r)
    rw [coeff_cuspPeriodPolynomial hk g' r hj, MvPolynomial.coeff_smul,
      coeff_cuspPeriodPolynomial hk g r hj, smul_eq_mul] at this
    linear_combination this
  have hg'eq : g' = e (γ.val 1 1 : ZMod N) • g := hinj (by rw [hIg', map_smul])
  rw [hg' z, hg'eq]
  change _ * (e (γ.val 1 1 : ZMod N) • g z) = _
  rw [smul_eq_mul]
  all_goals ring
