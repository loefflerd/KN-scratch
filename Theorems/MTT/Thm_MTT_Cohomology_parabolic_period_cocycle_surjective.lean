/-
Based on Prove2Me node MTT.Cohomology.parabolic_period_cocycle_surjective
(4ee25e36-bb36-4415-a38b-3e99005cb1da) by cbirkbeck (2026-09-07).

Proof based on Prove2Me submission 29fcf932-b652-4c39-be8e-013660f0d184
by cbirkbeck (2026-09-07); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import Definitions.MTT.Def_MTT_Cohomology_Integration

import Definitions.MTT.Def_MTT_ParabolicCohomology
import Theorems.MTT.Thm_MTT_Cohomology_integration_map
import Theorems.MTT.Thm_MTT_Cohomology_parabolicH1_finiteDimensional
import Theorems.MTT.Thm_MTT_Cohomology_parabolicH1_finrank_le
import Definitions.MTT.Def_MTT_Cohomology
import Theorems.MTT.Thm_MTT_Cohomology_reflection_class
import Theorems.MTT.Thm_MTT_Cohomology_period_cocycle_injective
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Parabolic Eichler–Shimura surjectivity in explicit period-cocycle form

Theorem statement: `MTT.Cohomology.parabolic_period_cocycle_surjective`
(`4ee25e36-bb36-4415-a38b-3e99005cb1da`), by cbirkbeck, 2026-09-07.

Proof: submission `29fcf932-b652-4c39-be8e-013660f0d184`, by cbirkbeck, 2026-09-07 (ACCEPTED);
locally adapted.

Let $N\ge1$, $k\ge2$, $n=k-2$, $\Gamma=\Gamma_1(N)$, and $V_n$ be the homogeneous degree-$n$
polynomials in $\mathbf C[X,Y]$. Use the left action
$$\begin{pmatrix}a&b\\c&d\end{pmatrix}\cdot Q(X,Y)=Q(aX+cY,bX+dY).$$
Let $c:\Gamma\to V_n$ be a group cocycle, so
$$c(\gamma\delta)=c(\gamma)+\gamma\cdot c(\delta).$$
Assume it is parabolic: whenever $\gamma$ fixes a cusp $x\in\mathbf P^1(\mathbf Q)$, there is $Q\in
V_n$ with $c(\gamma)=\gamma\cdot Q-Q$.

For a cusp form $f$, let $P_f(\infty)=0$ and
$$P_f(r)=2\pi\int_0^\infty f(r+it)((r+it)X+Y)^n\,dt\quad(r\in\mathbf Q).$$
Write $\rho=\operatorname{diag}(-1,1)$, acting by $r\mapsto-r$ on finite cusps and fixing infinity.
Then there exist $g,h\in S_k(\Gamma)$ and $P\in V_n$ such that, for all $\gamma\in\Gamma$,
$$c(\gamma)=P_g(\gamma\infty)+\rho\cdot P_h(\rho\gamma\infty)+\gamma\cdot P-P.$$
Thus every parabolic group-cohomology class is represented by holomorphic and reflected cusp-form
periods. The principal correction $P$ makes the statement an equality of cocycles, not merely of
cohomology classes.

## Explanation of the source proof

# Surjectivity from injectivity and the parabolic dimension bound

This is a proof-sketch with two explicit open mathematical prerequisites:
`MTT.Cohomology.period_cocycle_injective` and
`MTT.Cohomology.parabolicH1_finrank_le`. The quotient construction, period-map
construction, and all steps reducing the stated surjectivity to those inputs
are proved in Lean. The separate finite-dimensionality theorem has a direct
accepted proof, submission `68146ab0-259d-482c-8a19-302f07939975`.

## The parabolic cohomology space

Put $V=\operatorname{Sym}^{k-2}(\mathbf C^2)$ with the MTT left substitution
action, and $\Gamma=\Gamma_1(N)$. In `Def_MTT_ParabolicCohomology`, ordinary
one-cocycles use mathlib's `Rep` and `groupCohomology.cocycles₁`. Impose the
parabolic condition that for each cusp $x$ and each $\gamma$ fixing $x$,
$c(\gamma)$ lies in the image of $\rho(\gamma)-1$. Quotient this subspace by
the principal cocycles $dP(\gamma)=\rho(\gamma)P-P$. The constructor API proves
that every principal cocycle is parabolic, so this is the usual quotient,
not a weakened substitute. Write it as $H^1_{\mathrm{par}}(\Gamma,V)$.

Its finite-dimensionality is independent of Eichler–Shimura: $\mathrm{SL}_2(\mathbf Z)$
is finitely generated, Schreier's theorem applies to its finite-index subgroup
$\Gamma$, and a cocycle is determined by its values on finitely many generators.
Thus the cocycle space embeds in a finite product of $V$. Subspaces and quotients
preserve finite-dimensionality.

## Constructing the period map

The already-proved normalized integration-map theorem supplies a linear map
$I:S_k(\Gamma)\to H_c$ satisfying `IntegralClass`. Coefficient extensionality and
the modular-symbol relation identify $I(f)(x,y)$ with
$P_f(y)-P_f(x)$, where $P_f$ is the exact MTT cusp primitive, including its
binomial coefficients and integral normalization. The already-proved reflection
theorem defines a linear endomorphism of $H_c$.

For any modular symbol $\varphi$, the function
$\gamma\mapsto\varphi(\infty,\gamma\infty)$ is a one-cocycle. At a cusp fixed
by $\gamma$, the witness for its being principal is $\varphi(x,\infty)$.
Consequently the sum of the integration symbol and the reflected integration
symbol defines a linear map

$$E:S_k(\Gamma)\oplus S_k(\Gamma)\longrightarrow H^1_{\mathrm{par}}(\Gamma,V).$$

The lemma `eichlerShimuraCocycle_apply` verifies that its representative is
exactly the two primitive terms in the target statement. In particular,
reflection fixes infinity; there is no extra endpoint constant or sign.

## Injectivity and dimensions

If $E(g,h)=0$, its representative is principal. The open theorem
`period_cocycle_injective` therefore gives $g=h=0$. This proves injectivity
of $E$ conditionally on that explicit input.

The other open input is the independent inequality

$$\dim_{\mathbf C}H^1_{\mathrm{par}}(\Gamma,V)
\le 2\dim_{\mathbf C}S_k(\Gamma).$$

It contains no reference to $E$ or its surjectivity. Since the target is
finite-dimensional, injectivity first proves that the domain, and hence each
cusp-form summand, is finite-dimensional. Injectivity gives the opposite
dimension inequality; the dimension of the product is the sum of the two
dimensions. Thus the dimensions are equal, and the standard linear-algebra
criterion gives surjectivity of $E$.

## Recovering the exact cocycle identity

Lift the given $c$ to the parabolic cocycle submodule and choose $(g,h)$ whose
class under $E$ is its quotient class. Equality in the quotient says that
$c-E(g,h)$ lies in the principal-cocycle submodule. Its witness is a homogeneous
polynomial $P$, and rearranging gives
$c(\gamma)=E(g,h)(\gamma)+\rho(\gamma)P-P$, exactly as required. All witnesses
are retained, including the membership of $P$ in the symmetric-power space.

## Sources, scope, and verification

The argument follows the injectivity-plus-dimensions proof of Theorem 1,
§1.2, pp. 8–10 of the [Columbia Spring 2021 Eichler–Shimura
notes](https://www.math.columbia.edu/~dmarcil/Seminars/2021_Spring/Notes/Week4-5.pdf).
The dimension equality used on p. 9 is isolated here as an OPEN upper-bound
obligation; this submission does not claim to prove that dimension formula.
The parabolic cocycle definitions correspond to §1.1 of those notes.
Weight two, small positive levels, and odd weights remain in the statements.
No torsion-free or even-weight assumption is added.

The exact standalone solution compiles against the pinned Lean 4.33.1/mathlib
environment. It imports no target or ancestor theorem, introduces no `sorry`
or custom axiom in its proof body, and adds no heartbeat or recursion override.
The only unresolved mathematical inputs are the two named platform children.
The dependency graph was checked for cycles before submission. The analytic
injectivity branch remains with the other active worker; this contribution
isolates the independent dimension branch and proves its algebraic reduction.

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
# The MTT period map into parabolic cohomology

The cocycle attached to a modular symbol is evaluated at (infinity, gamma infinity).
Its principal restriction at a fixed cusp has the explicit witness phi(x, infinity).
Passing to the quotient gives the ordinary Eichler–Shimura period map. No
injectivity or surjectivity is assumed in its construction.
-/

noncomputable section

namespace MTT.Cohomology

private theorem reflection_mem {N n : ℕ} (φ : Hc N n ℂ) :
    reflection φ.val ∈ Hc N n ℂ := by
  obtain ⟨ψ, hψ⟩ := (reflection_class φ).1
  rw [← hψ]
  exact ψ.property

/-- Reflection as a linear endomorphism of the modular-symbol space. -/
def reflectionLinearMap (N n : ℕ) : Hc N n ℂ →ₗ[ℂ] Hc N n ℂ where
  toFun φ := ⟨reflection φ.val, reflection_mem φ⟩
  map_add' φ ψ := by
    apply Subtype.ext
    funext D
    exact map_add _ _ _
  map_smul' a φ := by
    apply Subtype.ext
    funext D
    change act (R := ℂ) !![-1, 0; 0, 1] (a • _) = _
    exact map_smul (act (R := ℂ) !![-1, 0; 0, 1]) a _

private theorem symbol_cocycle_mem {N n : ℕ} (φ : Hc N n ℂ) :
    (fun γ : CongruenceSubgroup.Gamma1 N =>
      (⟨φ.val (OnePoint.infty, cuspAct γ.val OnePoint.infty), φ.property.1 _ _⟩ :
        gammaOneRep N n)) ∈ parabolicCocycles N n := by
  apply (mem_parabolicCocycles_iff _).mpr
  constructor
  · intro γ δ
    apply Subtype.ext
    exact (modularSymbol_groupCocycle φ OnePoint.infty γ δ).trans (add_comm _ _)
  · intro x γ hx
    refine ⟨⟨φ.val (x, OnePoint.infty), φ.property.1 _ _⟩, ?_⟩
    apply Subtype.ext
    exact modularSymbol_cuspStabilizer φ OnePoint.infty x γ hx

/-- Evaluation of a modular symbol gives a parabolic group cocycle. -/
def symbolToParabolicCocycle (N n : ℕ) : Hc N n ℂ →ₗ[ℂ] parabolicCocycles N n where
  toFun φ := ⟨fun γ => ⟨φ.val (OnePoint.infty, cuspAct γ.val OnePoint.infty),
    φ.property.1 _ _⟩, symbol_cocycle_mem φ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The sum of the holomorphic and reflected period cocycles. -/
def eichlerShimuraCocycle {N k : ℕ}
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k - 2) ℂ) :
    (CuspForm (MTT.GammaOne N) (k : ℤ) × CuspForm (MTT.GammaOne N) (k : ℤ)) →ₗ[ℂ]
      parabolicCocycles N (k - 2) :=
  (symbolToParabolicCocycle N (k - 2)).comp
    (I.comp (LinearMap.fst ℂ _ _) +
      (reflectionLinearMap N (k - 2)).comp (I.comp (LinearMap.snd ℂ _ _)))

/-- The Eichler–Shimura map into the quotient by principal cocycles. -/
def eichlerShimuraMap {N k : ℕ}
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k - 2) ℂ) :
    (CuspForm (MTT.GammaOne N) (k : ℤ) × CuspForm (MTT.GammaOne N) (k : ℤ)) →ₗ[ℂ]
      ParabolicH1 N (k - 2) :=
  (parabolicCoboundaries N (k - 2)).mkQ.comp (eichlerShimuraCocycle I)

theorem eichlerShimuraCocycle_apply {N k : ℕ} (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k - 2) ℂ)
    (hI : ∀ f, IntegralClass f (I f))
    (f : CuspForm (MTT.GammaOne N) (k : ℤ) × CuspForm (MTT.GammaOne N) (k : ℤ))
    (γ : CongruenceSubgroup.Gamma1 N) :
    ((eichlerShimuraCocycle I f).val γ).val =
      cuspPrimitive f.1 (cuspAct γ.val OnePoint.infty) +
        act !![-1, 0; 0, 1] (cuspPrimitive f.2
          (fractional !![-1, 0; 0, 1] (cuspAct γ.val OnePoint.infty))) := by
  change (I f.1).val _ + reflection (I f.2).val _ = _
  rw [MTT.IntegralClass.val_eq_integrationCochain hk _ _ (hI f.1),
    MTT.IntegralClass.val_eq_integrationCochain hk _ _ (hI f.2)]
  have hrho : fractional !![-1, 0; 0, 1] OnePoint.infty = OnePoint.infty := rfl
  have hz (g : CuspForm (MTT.GammaOne N) (k : ℤ)) : cuspPrimitive g OnePoint.infty = 0 := rfl
  simp only [reflection, integrationCochain, hrho, hz, sub_zero]

end MTT.Cohomology
end
end

section
/-!
# Surjectivity from the parabolic-cohomology dimension bound

The period-cocycle injectivity theorem remains an explicit platform dependency.
Finite-dimensionality of the parabolic target is proved independently. The
remaining dimension inequality is the Riemann–Roch/group-cohomology input in
the proof of Eichler–Shimura, not an assumed surjectivity assertion.
-/

noncomputable section

namespace MTT.Cohomology

theorem eichlerShimuraMap_injective {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k - 2) ℂ)
    (hI : ∀ f, IntegralClass f (I f)) : Function.Injective (eichlerShimuraMap I) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro f hf
  change eichlerShimuraCocycle I f ∈
    LinearMap.ker (parabolicCoboundaries N (k - 2)).mkQ at hf
  rw [Submodule.ker_mkQ] at hf
  obtain ⟨P, hP⟩ := (mem_parabolicCoboundaries_iff _).mp hf
  have hc γ := congrArg Subtype.val (hP γ)
  simp only [eichlerShimuraCocycle_apply hk I hI] at hc
  obtain ⟨hg, hh⟩ := period_cocycle_injective hN hk f.1 f.2 P.val P.property hc
  exact Prod.ext hg hh

theorem eichlerShimuraMap_surjective_of_finrank_le {N k : ℕ}
    (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k - 2) ℂ)
    (hI : ∀ f, IntegralClass f (I f))
    (hdim : Module.finrank ℂ (ParabolicH1 N (k - 2)) ≤
      2 * Module.finrank ℂ (CuspForm (MTT.GammaOne N) (k : ℤ))) :
    Function.Surjective (eichlerShimuraMap I) := by
  have : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have := parabolicH1_finiteDimensional (n := k - 2) hN
  have hinj := eichlerShimuraMap_injective hN hk I hI
  have := FiniteDimensional.of_injective (eichlerShimuraMap I) hinj
  have : FiniteDimensional ℂ (CuspForm (MTT.GammaOne N) (k : ℤ)) :=
    FiniteDimensional.of_injective
      (LinearMap.inl ℂ (CuspForm (MTT.GammaOne N) (k : ℤ))
        (CuspForm (MTT.GammaOne N) (k : ℤ))) LinearMap.inl_injective
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank _).mp hinj
  apply le_antisymm (LinearMap.finrank_le_finrank_of_injective hinj)
  simpa only [Module.finrank_prod, two_mul] using hdim

theorem parabolic_period_cocycle_surjective_of_finrank_le {N k : ℕ}
    (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k - 2) ℂ)
    (hI : ∀ f, IntegralClass f (I f))
    (hdim : Module.finrank ℂ (ParabolicH1 N (k - 2)) ≤
      2 * Module.finrank ℂ (CuspForm (MTT.GammaOne N) (k : ℤ)))
    (c : CongruenceSubgroup.Gamma1 N → Binary ℂ)
    (hsym : ∀ γ, c γ ∈ Sym ℂ (k - 2))
    (hcoc : ∀ γ δ, c (γ * δ) = c γ + act γ.val.val (c δ))
    (hpar : ∀ (x : Cusp) (γ : CongruenceSubgroup.Gamma1 N), cuspAct γ.val x = x →
      ∃ Q : Binary ℂ, Q ∈ Sym ℂ (k - 2) ∧ c γ = act γ.val.val Q - Q) :
    ∃ (g h : CuspForm (MTT.GammaOne N) (k : ℤ)) (P : Binary ℂ),
      P ∈ Sym ℂ (k - 2) ∧ ∀ γ : CongruenceSubgroup.Gamma1 N,
        c γ = cuspPrimitive g (cuspAct γ.val OnePoint.infty) +
          act !![-1, 0; 0, 1] (cuspPrimitive h
            (fractional !![-1, 0; 0, 1] (cuspAct γ.val OnePoint.infty))) +
          (act γ.val.val P - P) := by
  let z : parabolicCocycles N (k - 2) := ⟨fun γ => ⟨c γ, hsym γ⟩, by
    apply (mem_parabolicCocycles_iff _).mpr
    constructor
    · intro γ δ
      exact Subtype.ext ((hcoc γ δ).trans (add_comm _ _))
    · intro x γ hx
      obtain ⟨Q, hQ, heq⟩ := hpar x γ hx
      exact ⟨⟨Q, hQ⟩, Subtype.ext heq⟩⟩
  obtain ⟨f, hf⟩ := eichlerShimuraMap_surjective_of_finrank_le hN hk I hI hdim
    ((parabolicCoboundaries N (k - 2)).mkQ z)
  have hz : z - eichlerShimuraCocycle I f ∈ parabolicCoboundaries N (k - 2) := by
    rw [← Submodule.ker_mkQ (parabolicCoboundaries N (k - 2)), LinearMap.mem_ker, map_sub]
    change _ - eichlerShimuraMap I f = 0
    rw [hf, sub_self]
  obtain ⟨P, hP⟩ := (mem_parabolicCoboundaries_iff _).mp hz
  refine ⟨f.1, f.2, P.val, P.property, fun γ => ?_⟩
  have heq := congrArg Subtype.val (hP γ)
  change c γ - ((eichlerShimuraCocycle I f).val γ).val = act γ.val.val P.val - P.val at heq
  rw [eichlerShimuraCocycle_apply hk I hI] at heq
  exact sub_eq_iff_eq_add'.mp heq

end MTT.Cohomology
end
end

noncomputable section
open MTT.Cohomology

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (c : CongruenceSubgroup.Gamma1 N → Binary ℂ)
    (hsym : ∀ γ, c γ ∈ MTT.Cohomology.Sym ℂ (k - 2))
    (hcoc : ∀ γ δ, c (γ * δ) = c γ + act γ.val.val (c δ))
    (hpar : ∀ (x : Cusp) (γ : CongruenceSubgroup.Gamma1 N), cuspAct γ.val x = x →
      ∃ Q : Binary ℂ, Q ∈ MTT.Cohomology.Sym ℂ (k - 2) ∧ c γ = act γ.val.val Q - Q) :
    ∃ (g h : CuspForm (MTT.GammaOne N) (k : ℤ)) (P : Binary ℂ),
      P ∈ MTT.Cohomology.Sym ℂ (k - 2) ∧ ∀ γ : CongruenceSubgroup.Gamma1 N,
        c γ = cuspPrimitive g (cuspAct γ.val OnePoint.infty) +
          act !![-1, 0; 0, 1] (cuspPrimitive h
            (fractional !![-1, 0; 0, 1] (cuspAct γ.val OnePoint.infty))) +
          (act γ.val.val P - P) := by
  obtain ⟨I, _, _, hI⟩ := MTT.Cohomology.integration_map hN hk
  exact MTT.Cohomology.parabolic_period_cocycle_surjective_of_finrank_le hN hk I hI
    (MTT.Cohomology.parabolicH1_finrank_le hN hk) c hsym hcoc hpar
end

end privateSection

public section publicSection

noncomputable section
open MTT.Cohomology
theorem MTT.Cohomology.parabolic_period_cocycle_surjective
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (c : CongruenceSubgroup.Gamma1 N → Binary ℂ)
    (hsym : ∀ γ, c γ ∈ Sym ℂ (k - 2))
    (hcoc : ∀ γ δ, c (γ * δ) = c γ + act γ.val.val (c δ))
    (hpar : ∀ (x : Cusp) (γ : CongruenceSubgroup.Gamma1 N), cuspAct γ.val x = x →
      ∃ Q : Binary ℂ, Q ∈ Sym ℂ (k - 2) ∧ c γ = act γ.val.val Q - Q) :
    ∃ (g h : CuspForm (MTT.GammaOne N) (k : ℤ)) (P : Binary ℂ),
      P ∈ Sym ℂ (k - 2) ∧ ∀ γ : CongruenceSubgroup.Gamma1 N,
        c γ = cuspPrimitive g (cuspAct γ.val OnePoint.infty) +
          act !![-1, 0; 0, 1] (cuspPrimitive h
            (fractional !![-1, 0; 0, 1] (cuspAct γ.val OnePoint.infty))) +
          (act γ.val.val P - P) := _root_.solution hN hk c hsym hcoc hpar
end

end publicSection
