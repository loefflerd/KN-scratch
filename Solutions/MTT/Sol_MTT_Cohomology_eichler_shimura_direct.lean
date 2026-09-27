import Definitions.MTT.Def_MTT_Cohomology_Integration
import Definitions.MTT.Def_MTT_Cohomology_Boundary
import Theorems.MTT.Thm_MTT_Cohomology_period_cocycle_injective

section
/-!
# Identifying the normalized integral class

Extracted from our accepted Hecke-equivariance proof, submission
409661e4-aebb-482e-a7ec-21de19561db6. No analytic input is used here.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MTT.Cohomology
namespace MTT.IntegralClass

private lemma coeff_cusp_period_polynomial {N k : ℕ} (hk : 2 ≤ k)
    (f : CuspForm (GammaOne N) (k : ℤ)) (r : ℚ) {j : ℕ} (hj : j ≤ k - 2) :
    MvPolynomial.coeff (binaryExponent (k - 2) j) (cuspPeriodPolynomial f r) =
      ((k - 2).choose j : ℂ) * modularIntegral f (Polynomial.X ^ j) r := by
  rw [cuspPeriodPolynomial, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [if_neg]
    intro h
    exact hij (by simpa [binaryExponent] using congrArg (fun v => v 0) h)
  · intro hj'
    exact absurd (Finset.mem_range.mpr (by omega)) hj'

private lemma cusp_period_polynomial_mem_sym {N k : ℕ} (hk : 2 ≤ k)
    (f : CuspForm (GammaOne N) (k : ℤ)) (r : ℚ) :
    cuspPeriodPolynomial f r ∈ MTT.Cohomology.Sym ℂ (k - 2) := by
  unfold cuspPeriodPolynomial
  refine Submodule.sum_mem _ fun j hj => ?_
  rw [MvPolynomial.mem_homogeneousSubmodule]
  apply MvPolynomial.isHomogeneous_monomial
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  have := Finset.mem_range.mp hj
  simp [binaryExponent]
  omega

private lemma sym_ext {n : ℕ} {P Q : Binary ℂ}
    (hP : P ∈ MTT.Cohomology.Sym ℂ n) (hQ : Q ∈ MTT.Cohomology.Sym ℂ n)
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

theorem val_eq_integrationCochain {N k : ℕ} (hk : 2 ≤ k)
    (f : CuspForm (GammaOne N) (k : ℤ)) (φ : Hc N (k - 2) ℂ)
    (hφ : IntegralClass f φ) : φ.val = integrationCochain f := by
  obtain ⟨hsym, hcocy, -⟩ := φ.2
  have hval (x : Cusp) : φ.val (OnePoint.infty, x) = cuspPrimitive f x := by
    rcases x with _ | r
    · exact add_eq_left.mp (hcocy OnePoint.infty OnePoint.infty OnePoint.infty)
    · apply sym_ext (hsym _ _) (cusp_period_polynomial_mem_sym hk f r)
      intro j hj
      change evaluation j r φ = _
      rw [hφ j r hj, coeff_cusp_period_polynomial hk f r hj]
  funext D
  have h := hcocy OnePoint.infty D.1 D.2
  rw [hval, hval] at h
  exact eq_sub_of_add_eq' h

end MTT.IntegralClass
end
end

section
/-!
# Directness from injectivity of the period cocycle

Evaluating a vanishing sum at `(∞, γ∞)` turns an equivariant boundary datum
into a single principal cocycle. The remaining analytic input is explicit.
-/

set_option autoImplicit false
noncomputable section
open MTT.Cohomology

theorem MTT.Cohomology.eichler_shimura_direct_reduction
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k - 2) ℂ)
    (hI : ∀ f, IntegralClass f (I f))
    (g h : CuspForm (MTT.GammaOne N) (k : ℤ)) (Φ : Cusp → Binary ℂ)
    (hΦ : IsBoundaryDatum N (k - 2) Φ)
    (hsum : (I g).val + reflection (I h).val + boundaryCochain Φ = 0) :
    g = 0 ∧ h = 0 ∧ boundaryCochain Φ = 0 := by
  have hcochain : integrationCochain g + reflection (integrationCochain h) +
      boundaryCochain Φ = 0 := by
    simpa only [MTT.IntegralClass.val_eq_integrationCochain hk g (I g) (hI g),
      MTT.IntegralClass.val_eq_integrationCochain hk h (I h) (hI h)] using hsum
  obtain ⟨hg, hh⟩ := period_cocycle_injective hN hk g h (-Φ OnePoint.infty)
    ((Sym ℂ (k - 2)).neg_mem (hΦ.1 _)) (fun γ => by
      have heq := congrFun hcochain (OnePoint.infty, cuspAct γ.val OnePoint.infty)
      have hrho : fractional !![-1, 0; 0, 1] OnePoint.infty = OnePoint.infty := rfl
      have hz (f : CuspForm (MTT.GammaOne N) (k : ℤ)) :
          cuspPrimitive f OnePoint.infty = 0 := rfl
      simp only [Pi.add_apply, Pi.zero_apply, integrationCochain, reflection,
        hrho, hz, sub_zero, boundaryCochain, hΦ.2] at heq
      rw [map_neg]
      linear_combination heq)
  refine ⟨hg, hh, ?_⟩
  have hR : reflection (0 : (Cusp × Cusp) → Binary ℂ) = 0 := by
    funext D
    exact map_zero _
  simpa [hg, hh, hR] using hsum
end
end

noncomputable section
open MTT.Cohomology

theorem solution {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k - 2) ℂ)
    (hI : ∀ f, IntegralClass f (I f))
    (g h : CuspForm (MTT.GammaOne N) (k : ℤ)) (Φ : Cusp → Binary ℂ)
    (hΦ : IsBoundaryDatum N (k - 2) Φ)
    (hsum : (I g).val + reflection (I h).val + boundaryCochain Φ = 0) :
    g = 0 ∧ h = 0 ∧ boundaryCochain Φ = 0 :=
  eichler_shimura_direct_reduction hN hk I hI g h Φ hΦ hsum

