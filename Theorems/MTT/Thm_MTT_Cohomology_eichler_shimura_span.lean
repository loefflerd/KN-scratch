module

public import Definitions.MTT.Def_MTT_Cohomology_Boundary

import Definitions.MTT.Def_MTT_Cohomology_Integration
import Definitions.MTT.Def_MTT_Cohomology
import Theorems.MTT.Thm_MTT_Cohomology_reflection_class
import Theorems.MTT.Thm_MTT_Cohomology_parabolic_period_cocycle_surjective

section privateSection

section
/-!
# Identifying the normalized integral class

Extracted from our accepted Hecke-equivariance proof, submission
409661e4-aebb-482e-a7ec-21de19561db6. No analytic input is used here.
-/

noncomputable section
open scoped BigOperators
open MTT.Cohomology
namespace MTT.IntegralClass

private lemma coeff_cusp_period_polynomial {N k : ℕ} (hk : 2 ≤ k)
    (f : CuspForm (GammaOne N) (k : ℤ)) (r : ℚ) {j : ℕ} (hj : j ≤ k - 2) :
    AddMonoidAlgebra.coeff (cuspPeriodPolynomial f r) (binaryExponent (k - 2) j) =
      ((k - 2).choose j : ℂ) * modularIntegral f (Polynomial.X ^ j) r := by
  rw [cuspPeriodPolynomial, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [ite_eq_right]
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
# Boundary symbols and principal period cocycles

The kernel computation in the boundary exact sequence is valid over every
commutative coefficient ring. No analytic input is used.
-/

noncomputable section
namespace MTT.Cohomology

theorem isBoundary_iff_period_coboundary {N n : ℕ} {R : Type*} [CommRing R]
    (φ : Hc N n R) :
    (∃ Φ : Cusp → Binary R, IsBoundaryDatum N n Φ ∧ φ.val = boundaryCochain Φ) ↔
    ∃ P : Binary R, P ∈ Sym R n ∧
      ∀ γ : CongruenceSubgroup.Gamma1 N,
        φ.val (OnePoint.infty, cuspAct γ.val OnePoint.infty) = act γ.val.val P - P := by
  constructor
  · rintro ⟨Φ, hΦ, hφ⟩
    rw [hφ]
    exact ⟨Φ OnePoint.infty, hΦ.1 _, fun γ => by
      simp only [boundaryCochain, hΦ.2]⟩
  · rintro ⟨P, hP, hcob⟩
    let Φ : Cusp → Binary R := fun x => φ.val (OnePoint.infty, x) + P
    refine ⟨Φ, ⟨fun x => (Sym R n).add_mem (φ.2.1 _ _) hP, ?_⟩, ?_⟩
    · intro γ x
      have h := φ.2.2.1 OnePoint.infty (cuspAct γ.val OnePoint.infty) (cuspAct γ.val x)
      rw [hcob γ, φ.2.2.2 γ OnePoint.infty x] at h
      change φ.val (OnePoint.infty, cuspAct γ.val x) + P =
        act γ.val.val (φ.val (OnePoint.infty, x) + P)
      rw [map_add, ← h]
      abel
    · funext D
      have h := φ.2.2.1 OnePoint.infty D.1 D.2
      change φ.val D = (φ.val (OnePoint.infty, D.2) + P) -
        (φ.val (OnePoint.infty, D.1) + P)
      rw [← h]
      abel

end MTT.Cohomology
end
end

section
/-!
# The group cocycle attached to a modular symbol

The base cusp is arbitrary. The cocycle is principal on each cusp stabilizer.
-/

noncomputable section
namespace MTT.Cohomology

theorem modularSymbol_groupCocycle {N n : ℕ} {R : Type*} [CommRing R]
    (φ : Hc N n R) (b : Cusp) (γ δ : CongruenceSubgroup.Gamma1 N) :
    φ.val (b, cuspAct (γ * δ).val b) =
      φ.val (b, cuspAct γ.val b) + act γ.val.val (φ.val (b, cuspAct δ.val b)) := by
  have hact : cuspAct (γ * δ).val b = cuspAct γ.val (cuspAct δ.val b) := by
    simp only [cuspAct, Subgroup.coe_mul, map_mul, mul_smul]
  rw [hact, ← φ.2.2.1 b (cuspAct γ.val b), φ.2.2.2 γ]

theorem modularSymbol_cuspStabilizer {N n : ℕ} {R : Type*} [CommRing R]
    (φ : Hc N n R) (b x : Cusp) (γ : CongruenceSubgroup.Gamma1 N)
    (hx : cuspAct γ.val x = x) :
    φ.val (b, cuspAct γ.val b) = act γ.val.val (φ.val (x, b)) - φ.val (x, b) := by
  have h := φ.2.2.1 x b (cuspAct γ.val b)
  have heq := φ.2.2.2 γ x b
  rw [hx] at heq
  rw [heq] at h
  exact eq_sub_of_add_eq' h

end MTT.Cohomology
end
end

section
/-!
# Spanning from parabolic period-cocycle surjectivity

The boundary datum is reconstructed explicitly from the residual modular symbol.
-/

noncomputable section
open MTT.Cohomology

theorem MTT.Cohomology.eichler_shimura_span_reduction
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k - 2) ℂ)
    (hI : ∀ f, IntegralClass f (I f)) (φ : Hc N (k - 2) ℂ) :
    ∃ (g h : CuspForm (MTT.GammaOne N) (k : ℤ)) (Φ : Cusp → Binary ℂ),
      IsBoundaryDatum N (k - 2) Φ ∧
      φ.val = (I g).val + reflection (I h).val + boundaryCochain Φ := by
  let c : CongruenceSubgroup.Gamma1 N → Binary ℂ :=
    fun γ => φ.val (OnePoint.infty, cuspAct γ.val OnePoint.infty)
  obtain ⟨g, h, P, hP, hc⟩ := parabolic_period_cocycle_surjective hN hk c
    (fun γ => φ.2.1 _ _) (modularSymbol_groupCocycle φ OnePoint.infty)
    (fun x γ hx => ⟨φ.val (x, OnePoint.infty), φ.2.1 _ _,
      modularSymbol_cuspStabilizer φ OnePoint.infty x γ hx⟩)
  obtain ⟨Rh, hRh⟩ := (reflection_class (I h)).1
  let ψ : Hc N (k - 2) ℂ := φ - I g - Rh
  have hψ : ∀ γ : CongruenceSubgroup.Gamma1 N,
      ψ.val (OnePoint.infty, cuspAct γ.val OnePoint.infty) = act γ.val.val P - P := by
    intro γ
    have heq := hc γ
    have hrho : fractional !![-1, 0; 0, 1] OnePoint.infty = OnePoint.infty := rfl
    have hz (f : CuspForm (MTT.GammaOne N) (k : ℤ)) :
        cuspPrimitive f OnePoint.infty = 0 := rfl
    change φ.val _ - (I g).val _ - Rh.val _ = _
    rw [hRh, MTT.IntegralClass.val_eq_integrationCochain hk g (I g) (hI g),
      MTT.IntegralClass.val_eq_integrationCochain hk h (I h) (hI h)]
    simp only [reflection, integrationCochain, hrho, hz, sub_zero]
    change c γ - _ - _ = _
    linear_combination heq
  obtain ⟨Φ, hΦ, heq⟩ := (isBoundary_iff_period_coboundary ψ).mpr ⟨P, hP, hψ⟩
  refine ⟨g, h, Φ, hΦ, ?_⟩
  change φ.val - (I g).val - Rh.val = boundaryCochain Φ at heq
  rw [hRh] at heq
  linear_combination heq
end
end

noncomputable section
open MTT.Cohomology

theorem solution {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k - 2) ℂ)
    (hI : ∀ f, IntegralClass f (I f)) (φ : Hc N (k - 2) ℂ) :
    ∃ (g h : CuspForm (MTT.GammaOne N) (k : ℤ)) (Φ : Cusp → Binary ℂ),
      IsBoundaryDatum N (k - 2) Φ ∧
      φ.val = (I g).val + reflection (I h).val + boundaryCochain Φ :=
  eichler_shimura_span_reduction hN hk I hI φ
end

end privateSection

public section publicSection

noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.eichler_shimura_span
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ)
    (hI : ∀ f, IntegralClass f (I f)) (φ : Hc N (k-2) ℂ) :
    ∃ (g h : CuspForm (MTT.GammaOne N) (k : ℤ)) (Φ : Cusp → Binary ℂ),
      IsBoundaryDatum N (k-2) Φ ∧
      φ.val = (I g).val + reflection (I h).val + boundaryCochain Φ := _root_.solution hN hk I hI φ
end

end publicSection
