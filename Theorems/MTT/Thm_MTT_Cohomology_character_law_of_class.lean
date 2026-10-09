/-
Based on Prove2Me node MTT.Cohomology.character_law_of_class
(fef71a5c-0ea1-4b6a-9153-871fcdf8079d) by cbirkbeck (2026-09-06).

Proof based on Prove2Me submission 8a2b39af-927a-412f-a2d8-2d81baedab35
by cbirkbeck (2026-09-06); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import Definitions.MTT.Def_MTT_Cohomology

import Theorems.MTT.Thm_MTT_exists_cuspForm_slash_gamma0
import Theorems.MTT.Thm_MTT_Cohomology_cuspPrimitive_slash_relation
import Theorems.MTT.Thm_MTT_period_vanishing
import Theorems.MTT.Thm_MTT_Cohomology_evaluation_faithful
import Definitions.MTT.Def_MTT_Cohomology_Integration
import Mathlib.RingTheory.Flat.Basic

/-!
# The nebentype law on the modular symbol $I(g)$ descends to the cusp form $g$

Theorem statement: `MTT.Cohomology.character_law_of_class` (`fef71a5c-0ea1-4b6a-9153-871fcdf8079d`),
by cbirkbeck, 2026-09-06.

Proof: submission `8a2b39af-927a-412f-a2d8-2d81baedab35`, by cbirkbeck, 2026-09-06 (ACCEPTED);
locally adapted.

Let $N\ge1$, $k\ge2$, $n=k-2$, and let
$$I:S_k(\Gamma_1(N))\longrightarrow
H_c=\operatorname{Hom}_{\Gamma_1(N)}\big(\operatorname{Div}^0(\mathbf P^1(\mathbf
Q)),\operatorname{Sym}^n\mathbf C^2\big)$$
be any linear map with the integral-class property of the mission: for every cusp form $h$, every
$0\le j\le n$ and every $r\in\mathbf Q$, the coefficient of $X^jY^{n-j}$ in $I(h)(\infty,r)$ equals
$\binom nj$ times the modular integral $2\pi\int_0^\infty h(r+it)\,(r+it)^j\,dt$. Let $e:\mathbf
Z/N\mathbf Z\to\mathbf C$ be any function (in applications a Dirichlet character), and let $g\in
S_k(\Gamma_1(N))$ be a cusp form whose class satisfies the nebentype law
$$I(g)(\gamma x,\gamma y)=e(d)\,\gamma\cdot I(g)(x,y)\qquad\text{for all
}\gamma=\begin{pmatrix}a&b\\ c&d\end{pmatrix}\in\Gamma_0(N),\ x,y\in\mathbf P^1(\mathbf Q),$$
where $\gamma\cdot$ is the coefficient action on $\operatorname{Sym}^n$.

**Claim.** Then $g$ has nebentypus $e$:
$$g(\gamma z)=e(d)\,(cz+d)^k\,g(z)\qquad\text{for all }\gamma\in\Gamma_0(N),\ z\in\mathfrak H.$$

*Why this holds.* A modular symbol $\phi\in H_c$ is determined by its values $\phi(\infty,r)$,
$r\in\mathbf Q$, because $\phi(x,y)=\phi(\infty,y)-\phi(\infty,x)$ by the cocycle relation; hence
$I(g)$ is the classical modular symbol $\xi_g(x,y)=2\pi\int_x^y g(z)\,(zX+Y)^n\,dz$ of $g$ (Shimura,
§8.2; MTT, Chapter I §3). The change of variables $z\mapsto\gamma z$ in the integral gives the
$\Gamma_0(N)$-equivariance
$$\xi_{g|_k\gamma}(x,y)=\gamma^{-1}\cdot\xi_g(\gamma x,\gamma y),$$
where $g|_k\gamma\in S_k(\Gamma_1(N))$ because $\Gamma_1(N)$ is normal in $\Gamma_0(N)$. Combined
with the assumed law this gives $I(g|_k\gamma)=e(d)\,I(g)=I(e(d)\,g)$. Finally $I$ is injective—a
cusp form all of whose modular integrals $\int_0^\infty g(r+it)(r+it)^j\,dt$ vanish is zero (the
sibling problem `MTT.period_vanishing`)—so $g|_k\gamma=e(d)\,g$, which is the claim.

## Explanation of the source proof

We reduce the descent of the nebentype law from the modular symbol $I(g)$ to the form $g$ to two
lemmas, which are assumptions of this submission, plus the sibling problems `period_vanishing` and
(proved) `evaluation_faithful`:

- `MTT.exists_cuspForm_slash_gamma0`: for $\gamma=\begin{pmatrix}a&b\\
  c&d\end{pmatrix}\in\Gamma_0(N)$ the slash $g'=g|_k\gamma$ is a cusp form on $\Gamma_1(N)$, with
  $g(\gamma z)=(cz+d)^kg'(z)$.
- `MTT.Cohomology.cuspPrimitive_slash_relation`: the cusp primitive $P_g(x)=\int_\infty^x
  g(w)(wX+Y)^n\,dw$ (normalised as in the mission) satisfies $P_g(\gamma x)=\gamma\cdot
  P_{g'}(x)+P_g(\gamma\infty)$, the change of variables $w=\gamma z$ in the period integral.

**Step 1: the class is the primitive.** By the cocycle relation
$\phi(\infty,\infty)+\phi(\infty,\infty)=\phi(\infty,\infty)$ every class satisfies
$\phi(\infty,\infty)=0$, and the integral-class property says that the coefficient of $X^jY^{n-j}$
in $(Ig)(\infty,r)$ is $\binom nj$ times the modular integral, which is exactly the corresponding
coefficient of the period polynomial $P_g(r)$ (`coeff_cuspPeriodPolynomial`). Both are homogeneous
of degree $n$, and a homogeneous polynomial of degree $n$ in two variables is determined by these
coefficients (`Sym_ext`), so $(Ig)(\infty,s)=P_g(s)$ for every cusp $s$ (`hval`). The cocycle
relation then gives $(Ig)(x,y)=P_g(y)-P_g(x)$ for all cusps (`hcoc`).

**Step 2: the period polynomial of $g|\gamma$.** Evaluating the assumed law at $(\infty,r)$ and
using Step 1,
$$P_g(\gamma r)-P_g(\gamma\infty)=e(d)\,\gamma\cdot P_g(r),$$
while the slash relation gives $P_g(\gamma r)-P_g(\gamma\infty)=\gamma\cdot P_{g'}(r)$. Hence
$\gamma\cdot P_{g'}(r)=\gamma\cdot\big(e(d)P_g(r)\big)$. The coefficient action is a group action,
$A\cdot(B\cdot Q)=(AB)\cdot Q$ (`act_act`, by checking on the variables), so
$\operatorname{adj}(\gamma)\cdot$ inverts $\gamma\cdot$ when $\det\gamma=1$
(`act_injective_of_det_one`), and therefore $P_{g'}(r)=e(d)\,P_g(r)$ for every $r\in\mathbf Q$
(`hpoly`).

**Step 3: descent.** Comparing coefficients, the evaluations of $I(g')$ and of $e(d)\,I(g)$ agree
for all $j\le n$ and $r$, so $I(g')=e(d)\,I(g)=I(e(d)g)$ by `evaluation_faithful`. Any integration
map is injective because a cusp form with vanishing modular integrals is zero (`period_vanishing`,
via `injective_of_integralClass`), whence $g'=e(d)\,g$. Substituting into $g(\gamma
z)=(cz+d)^kg'(z)$ gives $g(\gamma z)=e(d)(cz+d)^kg(z)$, the nebentype law for $g$.

<!-- Generated by add_prove2me_provenance.py -->
-/

section privateSection

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
    have := congrArg ((fun p => AddMonoidAlgebra.coeff p (binaryExponent (k - 2) j))) (hpoly r)
    rw [coeff_cuspPeriodPolynomial hk g' r hj, MvPolynomial.coeff_smul,
      coeff_cuspPeriodPolynomial hk g r hj, smul_eq_mul] at this
    linear_combination this
  have hg'eq : g' = e (γ.val 1 1 : ZMod N) • g := hinj (by rw [hIg', map_smul])
  rw [hg' z, hg'eq]
  change _ * (e (γ.val 1 1 : ZMod N) • g z) = _
  rw [smul_eq_mul]
  all_goals ring
end

end privateSection

public section publicSection

noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.character_law_of_class
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
          (((γ.val 1 0 : ℤ) : ℂ) * z + ((γ.val 1 1 : ℤ) : ℂ)) ^ k * g z := _root_.solution hN hk I hI e g hlaw
end

end publicSection
