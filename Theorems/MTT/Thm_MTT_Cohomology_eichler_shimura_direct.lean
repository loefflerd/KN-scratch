/-
Based on Prove2Me node MTT.Cohomology.eichler_shimura_direct
(98189fbe-6dc1-4abe-aff4-a1ec348bb514) by cbirkbeck (2026-09-07).

Proof based on Prove2Me submission 85e05f31-f511-4d11-9d09-c01914a25f79
by cbirkbeck (2026-09-07); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import Definitions.MTT.Def_MTT_Cohomology_Boundary

import Definitions.MTT.Def_MTT_Cohomology_Integration
import Theorems.MTT.Thm_MTT_Cohomology_period_cocycle_injective

/-!
# Directness of the Eichler–Shimura decomposition of $H^1_c$: holomorphic, antiholomorphic and boundary classes are independent

Theorem statement: `MTT.Cohomology.eichler_shimura_direct` (`98189fbe-6dc1-4abe-aff4-a1ec348bb514`),
by cbirkbeck, 2026-09-07.

Proof: submission `85e05f31-f511-4d11-9d09-c01914a25f79`, by cbirkbeck, 2026-09-07 (ACCEPTED);
locally adapted.

Let $N\ge1$, $k\ge2$, $n=k-2$, and let $I:S_k(\Gamma_1(N))\to H_c$ be an integration map (a linear
map with the integral-class property, so that $I(g)$ is the modular symbol of $g$). Let $\mathcal R$
be the reflection induced by $\operatorname{diag}(-1,1)$ and let $\partial\Phi(x,y)=\Phi(y)-\Phi(x)$
be the boundary cochain of a $\Gamma_1(N)$-equivariant $\operatorname{Sym}^n$-valued function $\Phi$
on cusps.

**Claim (directness of the Eichler–Shimura decomposition).** If
$$I(g)+\mathcal R\big(I(h)\big)+\partial\Phi=0$$
for cusp forms $g,h$ and a boundary datum $\Phi$, then $g=0$, $h=0$ and $\partial\Phi=0$.

Together with `eichler_shimura_span` this says that
$H_c=\operatorname{Hom}_{\Gamma_1(N)}(\operatorname{Div}^0,\operatorname{Sym}^n)$ is the direct sum
of the holomorphic image, the antiholomorphic (reflected) image and the boundary (Eisenstein)
classes — the Eichler–Shimura isomorphism $H^1_c(\Gamma_1(N),\operatorname{Sym}^n)\cong
S_k\oplus\overline{S_k}\oplus\operatorname{Eis}$ (Ash–Stevens, Proposition 4.2; Williams, Theorem
11.5). The cuspidal part is detected by the Petersson pairing (the classes $I(g)$ and $\mathcal R
I(h)$ pair non-degenerately with $\overline{S_k}$ and $S_k$ respectively and are orthogonal to the
boundary classes), which is why the three pieces are independent.

## Explanation of the source proof

# Reduction to ordinary period-cocycle injectivity

This is a conditional proof-sketch, not a completed analytic proof. Its sole
theorem dependency is the open `MTT.Cohomology.period_cocycle_injective`.
It imports no directness theorem, spanning theorem, or descendant of either.

Write `P_f` for the mission's normalized homogeneous cusp primitive and
`ρ = diag(-1,1)`. The new child is the classical injectivity assertion that

\[
P_g(\gamma\infty)+\rho\cdot P_h(\rho\gamma\infty)
   =\gamma\cdot P-P\qquad(\gamma\in\Gamma_1(N))
\]

for one homogeneous polynomial `P` implies `g=h=0`. Unlike the parent, it
involves neither an arbitrary integration map nor an equivariant function on
all cusps. It is the analytic ordinary/parabolic-cohomology input, not a
claim that the remaining analysis has been formalized.

The submitted Lean file proves all of the following steps.

1. An integral class is exactly the explicit integration cochain
   `I(f)(x,y)=P_f(y)-P_f(x)`. The prescribed normalized coefficients determine
   its value at `(∞,r)`: homogeneous binary polynomials are determined by
   their degree-`k-2` monomials. The cocycle relation determines every other
   pair. This algebraic argument is extracted from our accepted proof
   `409661e4-aebb-482e-a7ec-21de19561db6`.
2. Evaluate the assumed zero sum at `(∞,γ∞)`. Reflection fixes infinity and
   acts on the coefficients by `ρ`, while equivariance of the boundary datum
   gives `Φ(γ∞)=γ·Φ(∞)`. Consequently the displayed identity holds with
   `P=-Φ(∞)`. Homogeneity of this `P` follows from the boundary-datum property.
3. The child gives `g=h=0`. Linearity of the integration map and vanishing of
   the reflection of the zero cochain then give `boundaryCochain Φ=0`.

The analytic source is Ash–Stevens, *Modular forms in characteristic ℓ and
special values of their L-functions*, Theorem 2.3, p. 853
([paper](https://math.bu.edu/people/ghs/papers/Mod_fms_char_ell.pdf)).
The cocycle construction and injectivity argument are written explicitly in
the Columbia Spring 2021 seminar notes, §1.2, Theorem 1, pp. 8–10
([notes](https://www.math.columbia.edu/~dmarcil/Seminars/2021_Spring/Notes/Week4-5.pdf)).
Changing a primitive's basepoint adds a principal cocycle. The homogeneous
left action here corresponds to the source's standard symmetric-power
representation. Reflection realizes the antiholomorphic summand, after
reparametrizing by `h^c(z)=conj(h(-conj(z)))`; signs and the common nonzero
normalization factor do not change the injectivity assertion.

The file compiles under Lean 4.33.1 and mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, without increased heartbeat limits.
It contains no `sorry`, `admit`, new axiom, or local `Solutions.*` import.
The only local placeholder in its dependency closure is the explicitly tracked
open child. The independent algebraic helper uses only Lean's usual
`propext`, `Classical.choice`, and `Quot.sound` axioms.

<!-- Generated by add_prove2me_provenance.py -->
-/

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
# Directness from injectivity of the period cocycle

Evaluating a vanishing sum at `(∞, γ∞)` turns an equivariant boundary datum
into a single principal cocycle. The remaining analytic input is explicit.
-/

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
end

end privateSection

public section publicSection

noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.eichler_shimura_direct
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ)
    (hI : ∀ f, IntegralClass f (I f))
    (g h : CuspForm (MTT.GammaOne N) (k : ℤ)) (Φ : Cusp → Binary ℂ)
    (hΦ : IsBoundaryDatum N (k-2) Φ)
    (hsum : (I g).val + reflection (I h).val + boundaryCochain Φ = 0) :
    g = 0 ∧ h = 0 ∧ boundaryCochain Φ = 0 := _root_.solution hN hk I hI g h Φ hΦ hsum
end

end publicSection
