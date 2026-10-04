import Theorems.MTT.Thm_MTT_Cohomology_integral_class_character_law
import Theorems.MTT.Thm_MTT_Cohomology_reflection_class
import Theorems.MTT.Thm_MTT_Cohomology_reflection_involutive
import Definitions.MTT.Def_MTT_Cohomology_Integration
import Mathlib.RingTheory.Flat.Basic
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

/-- The substitution underlying `act`, with its target algebra made explicit. -/
def actAlg (γ : Matrix (Fin 2) (Fin 2) ℤ) : Binary ℂ →ₐ[ℂ] Binary ℂ :=
  @MvPolynomial.aeval ℂ (Binary ℂ) (Fin 2) _ _ _
    (fun i : Fin 2 => ∑ a : Fin 2, ((γ a i : ℤ) : ℂ) • (MvPolynomial.X a : Binary ℂ))

lemma act_eq_actAlg (γ : Matrix (Fin 2) (Fin 2) ℤ) (P : Binary ℂ) : act γ P = actAlg γ P := rfl

lemma actAlg_refl_X0 : actAlg !![-1, 0; 0, 1] (MvPolynomial.X 0 : Binary ℂ) = - MvPolynomial.X 0 := by
  rw [actAlg, MvPolynomial.aeval_X, Fin.sum_univ_two]
  simp

lemma actAlg_refl_X1 : actAlg !![-1, 0; 0, 1] (MvPolynomial.X 1 : Binary ℂ) = MvPolynomial.X 1 := by
  rw [actAlg, MvPolynomial.aeval_X, Fin.sum_univ_two]
  simp

lemma actAlg_C (γ : Matrix (Fin 2) (Fin 2) ℤ) (c : ℂ) :
    actAlg γ (MvPolynomial.C c) = MvPolynomial.C c := by
  rw [actAlg, MvPolynomial.aeval_C]; rfl

lemma monomial_binaryExponent (n j : ℕ) (c : ℂ) :
    (MvPolynomial.monomial (binaryExponent n j) c : Binary ℂ) =
      MvPolynomial.C c * MvPolynomial.X 0 ^ j * MvPolynomial.X 1 ^ (n - j) := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun i => by simp), Fin.prod_univ_two,
    binaryExponent_apply_zero, binaryExponent_apply_one, mul_assoc]

/-- The reflection acts on `X^j Y^(n-j)` by `(-1)^j`. -/
lemma act_refl_monomial (n j : ℕ) (c : ℂ) :
    act !![-1, 0; 0, 1] (MvPolynomial.monomial (binaryExponent n j) c) =
      (-1 : ℂ) ^ j • MvPolynomial.monomial (binaryExponent n j) c := by
  rw [monomial_binaryExponent, act_eq_actAlg, map_mul, map_mul, map_pow, map_pow, actAlg_C,
    actAlg_refl_X0, actAlg_refl_X1, neg_pow, MvPolynomial.smul_eq_C_mul, map_pow, map_neg, map_one]
  ring

lemma coeff_act_refl {n : ℕ} {P : Binary ℂ} (hP : P ∈ Sym ℂ n) (j : ℕ) (hj : j ≤ n) :
    AddMonoidAlgebra.coeff (act !![-1, 0; 0, 1] P) (binaryExponent n j) =
      (-1 : ℂ) ^ j * AddMonoidAlgebra.coeff P (binaryExponent n j) := by
  conv_lhs => rw [Sym_as_sum hP]
  rw [map_sum]
  simp only [act_refl_monomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
    MvPolynomial.coeff_monomial, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [ite_eq_right, mul_zero]
    intro h
    exact hij (by simpa [binaryExponent_apply_zero] using congrArg (fun v => v 0) h)
  · intro hj'
    exact absurd (Finset.mem_range.mpr (by omega)) hj'

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

lemma slash_add {R : Type*} [CommRing R] (g : Matrix (Fin 2) (Fin 2) ℤ)
    (φ ψ : (Cusp × Cusp) → Binary R) : slash g (φ + ψ) = slash g φ + slash g ψ := by
  funext D; simp [slash]

lemma slash_smul {R : Type*} [CommRing R] (g : Matrix (Fin 2) (Fin 2) ℤ) (c : R)
    (φ : (Cusp × Cusp) → Binary R) : slash g (c • φ) = c • slash g φ := by
  funext D; simp [slash]

lemma primeHecke_add {R : Type*} [CommRing R] (e : R) (l : ℕ) (φ ψ : (Cusp × Cusp) → Binary R) :
    primeHecke e l (φ + ψ) = primeHecke e l φ + primeHecke e l ψ := by
  simp only [primeHecke, slash_add, Finset.sum_add_distrib, smul_add]
  abel

lemma primeHecke_smul {R : Type*} [CommRing R] (e : R) (l : ℕ) (c : R)
    (φ : (Cusp × Cusp) → Binary R) : primeHecke e l (c • φ) = c • primeHecke e l φ := by
  simp only [primeHecke, slash_smul, ← Finset.smul_sum, smul_add, smul_comm e c]

lemma sign_sq_eq_one (s : Bool) : (MTT.sign s : ℂ) * (MTT.sign s : ℂ) = 1 := by
  cases s <;> simp [MTT.sign]

end MTT.Cohomology

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ)
    (hI : ∀ f, IntegralClass f (I f)) (hT : HeckeEquivariant I)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) :
    ∃ φ : Bool → Hc N (k-2) ℂ, ∀ s,
      SignedClass f.form s (φ s) ∧
      Packet (fun d => ι (f.epsilon d)) (fun l => ι (f.coeff l)) s (φ s) := by
  set Φ : Hc N (k-2) ℂ := I f.form with hΦ
  obtain ⟨ψ, hψ⟩ := (MTT.Cohomology.reflection_class Φ).1
  obtain ⟨hsym, -, -⟩ := Φ.2
  -- the nebentype law for `Φ`, then for its reflection
  have hlawΦ : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      Φ.val (cuspAct γ.val x, cuspAct γ.val y) =
        ι (f.epsilon (γ.val 1 1 : ZMod N)) • act γ.val.val (Φ.val (x, y)) :=
    fun γ x y => MTT.Cohomology.integral_class_character_law hN hk ι f Φ (hI f.form) γ x y
  have hlawψ := (MTT.Cohomology.reflection_class Φ).2.2 (fun d => ι (f.epsilon d)) hlawΦ
  -- the Hecke equations for `Φ`, then for its reflection
  have hHΦ : ∀ l : ℕ, l.Prime → primeHecke (ι (f.epsilon l)) l Φ.val = ι (f.coeff l) • Φ.val := by
    intro l hl
    have := hT (f.epsilon.ringHomComp ι) l hl f.form (ι (f.coeff l) • f.form) (fun z => by
      change ι (f.coeff l) • f.form z = _
      rw [smul_eq_mul, ← f.eigen l hl z]; rfl)
    rw [map_smul] at this
    exact this.symm
  have hHψ : ∀ l : ℕ, l.Prime →
      primeHecke (ι (f.epsilon l)) l (reflection Φ.val) = ι (f.coeff l) • reflection Φ.val := by
    intro l hl
    rw [← (MTT.Cohomology.reflection_class Φ).2.1, hHΦ l hl, reflection_smul]
  -- the evaluations of the reflection
  have hevψ : ∀ j r, j ≤ k - 2 → evaluation j r ψ =
      (-1 : ℂ) ^ j * (((k-2).choose j : ℂ) * MTT.modularIntegral f.form (Polynomial.X ^ j) (-r)) := by
    intro j r hj
    change AddMonoidAlgebra.coeff (ψ.val (OnePoint.infty, (r : Cusp))) (binaryExponent (k-2) j) = _
    rw [hψ]
    simp only [reflection]
    rw [fractional_refl_infty, fractional_refl_coe,
      coeff_act_refl (hsym OnePoint.infty ((-r : ℚ) : Cusp)) j hj]
    congr 1
    exact hI f.form j (-r) hj
  refine ⟨fun s => (1 / 2 : ℂ) • (Φ + (MTT.sign s : ℂ) • ψ), fun s => ⟨?_, ?_, ?_, ?_⟩⟩
  · -- signed class
    intro j r hj
    rw [map_smul, map_add, map_smul, hI f.form j r hj, hevψ j r hj, smul_eq_mul, smul_eq_mul]
    unfold MTT.signedIntegral
    ring
  · -- Hecke
    intro l hl
    simp only [Submodule.coe_smul, Submodule.coe_add, hψ, primeHecke_smul, primeHecke_add,
      hHΦ l hl, hHψ l hl]
    module
  · -- nebentype law
    intro γ x y
    simp only [Submodule.coe_smul, Submodule.coe_add, hψ, Pi.smul_apply, Pi.add_apply, hlawΦ γ x y,
      hlawψ γ x y, map_add, map_smul]
    module
  · -- reflection eigenvalue
    simp only [Submodule.coe_smul, Submodule.coe_add, hψ, reflection_smul, reflection_add,
      MTT.Cohomology.reflection_involutive]
    have h1 : (MTT.sign true : ℂ) = 1 := by simp [MTT.sign]
    have h2 : (MTT.sign false : ℂ) = -1 := by simp [MTT.sign]
    cases s
    · rw [h2]; module
    · rw [h1]; module
