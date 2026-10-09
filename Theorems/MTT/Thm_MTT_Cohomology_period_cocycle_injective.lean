/-
Based on Prove2Me node MTT.Cohomology.period_cocycle_injective
(56049e95-d9c0-47d9-89b9-f70efb7a6436) by cbirkbeck (2026-09-07).

Proof based on Prove2Me submission 1a4848c6-c6a2-4954-a364-015ec1df6d74
by davidloeffler (2026-09-07); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import Definitions.MTT.Def_MTT_Cohomology_Integration

import Theorems.MTT.Thm_MTT_Cohomology_period_reflected_cusp_form
import Theorems.MTT.Thm_MTT_Cohomology_principal_period_equivariant_primitive
import Theorems.MTT.Thm_MTT_Cohomology_equivariant_primitive_pairings_zero
import Theorems.MTT.Thm_MTT_Cohomology_period_pairing_petersson_definite

/-!
# Eichler–Shimura injectivity: a principal mixed period cocycle has zero cusp forms

Theorem statement: `MTT.Cohomology.period_cocycle_injective`
(`56049e95-d9c0-47d9-89b9-f70efb7a6436`), by cbirkbeck, 2026-09-07.

Proof: submission `1a4848c6-c6a2-4954-a364-015ec1df6d74`, by davidloeffler, 2026-09-07 (ACCEPTED);
locally adapted.

Let $N\ge1$, $k\ge2$, $n=k-2$, and let $g,h\in S_k(\Gamma_1(N))$. Write $P_f(x)$ for the normalized
cusp primitive of $f$: it vanishes at infinity and for $r\in\mathbf Q$ is
$$P_f(r)=2\pi\int_0^\infty f(r+it)\big((r+it)X+Y\big)^n\,dt.$$
For a matrix $\gamma=\begin{pmatrix}a&b\\c&d\end{pmatrix}$ the coefficient action is $\gamma\cdot
Q(X,Y)=Q(aX+cY,bX+dY)$. Put $\rho=\operatorname{diag}(-1,1)$; it sends a finite cusp $r$ to $-r$ and
fixes infinity.

Suppose there is a homogeneous degree-$n$ polynomial $P\in\mathbf C[X,Y]$ such that, for every
$\gamma\in\Gamma_1(N)$,
$$P_g(\gamma\infty)+\rho\cdot P_h(\rho\gamma\infty)=\gamma\cdot P-P.$$
Then $g=h=0$.

Thus the sum of the holomorphic and reflected period cocycles cannot be a principal group cocycle
unless both cusp forms vanish. This is the injectivity assertion in ordinary/parabolic
Eichler–Shimura cohomology, expressed in the mission's homogeneous-polynomial, left-action and
normalized-integral conventions. There is no hypothesis about a boundary function on all cusps or a
chosen integration map.

## Explanation of the source proof

Let $N>0$, $k\ge2$, and $n=k-2$. Suppose $g,h\in S_k(\Gamma_1(N))$ and
$P\in\operatorname{Sym}^n\mathbb C^2$ satisfy

$$
F_g(\gamma\infty)+\rho\cdot F_h(\rho\gamma\infty)=\gamma\cdot P-P
\qquad(\gamma\in\Gamma_1(N)),\qquad \rho=\operatorname{diag}(-1,1).
$$

The desired conclusion is

$$g=h=0.$$

This reduction uses four open analytic lemmas. The principle is that an exact equivariant mixed
differential has zero pairing against every closed cuspidal test differential, whereas pairing each
component with its own conjugate gives a nonzero multiple of its Petersson norm. No dimension
formula or surjectivity theorem is used.

1. **Reflection: `MTT.Cohomology.period_reflected_cusp_form`.** There exists $v\in S_k(\Gamma_1(N))$
   with

   $$\overline{v(z)}=h(-\bar z),\qquad v=0\Longleftrightarrow h=0.$$

   If $L_z=zX+Y$ and $\jmath(z)=-\bar z$, then

   $$\rho\cdot\jmath^*(h(z)L_z^n\,dz)=-\overline{v(z)}L_{\bar z}^n\,d\bar z.$$

   Thus reflection supplies the antiholomorphic component with the required sign. The formal child
   asserts the existence and zero equivalence; the pullback identity follows by substituting
   $X\mapsto-X$ and $d(-\bar z)=-d\bar z$.

2. **An equivariant primitive: `MTT.Cohomology.principal_period_equivariant_primitive`.** The
   principal-cocycle hypothesis yields a polynomial-valued function $U$ with

   $$U(\gamma z)=\gamma\cdot U(z),\qquad dU=g(z)L_z^n\,dz-\overline{v(z)}L_{\bar z}^n\,d\bar z.$$

   The predicate `IsMixedPeriodPrimitive` states this coefficientwise using real Fréchet
   derivatives, together with homogeneity and at most polynomial growth in every cusp chart. For the
   proof of this child, extend the normalized cusp primitive to the upper half-plane. If $F$ is the
   mixed normalized interior primitive, its transformation defect is the displayed cusp cocycle.
   Then $F+P$ is equivariant, and dividing by $2\pi i$ gives $U$ with the unnormalized differential
   above. Polynomial growth is required for $U$; decay of $U$ itself is not asserted.

3. **Stokes vanishing: `MTT.Cohomology.equivariant_primitive_pairings_zero`.** Define the
   determinant contraction by

   $$B_n(A,B)=\sum_{j=0}^{n}\frac{(-1)^{n-j}A_jB_{n-j}}{\binom nj},\qquad
   A=\sum_{j=0}^n A_jX^jY^{n-j},\quad B=\sum_{j=0}^n B_jX^jY^{n-j}.$$

   For cusp forms $f,q$, write

   $$\mathcal B_n(f,q)=\int y^2 B_n\big(f(z)L_z^n,\overline{q(z)}L_{\bar z}^n\big)\,d\mu(z),\qquad
   d\mu=dx\,dy/y^2.$$

   The integration convention is the finite sum over inverse right-coset representatives for
   $\Gamma_1(N)$ in $\mathrm{SL}_2(\mathbb Z)$ of integrals on the standard modular fundamental
   region. This specifies the integral without introducing a quotient manifold. If $-I$ is absent
   from the group, this convention can count the geometric domain twice, consistently throughout the
   argument.

   The third child states

   $$\mathcal B_n(g,q)=\mathcal B_n(q,v)=0\qquad\text{for every cusp form }q.$$

   Its intended proof applies Stokes to the contraction of $U$ with the two opposite-type test
   differentials on truncated fundamental regions. Equivariance cancels paired sides. Polynomial
   growth of $U$ against the exponential decay of the test forms makes the cusp boundary terms tend
   to zero. The fixed nonzero factor from $dz\wedge d\bar z$ is removed in the definition of
   $\mathcal B_n$. Establishing the invariant contraction and these analytic cancellations remains
   part of this child.

4. **Petersson definiteness: `MTT.Cohomology.period_pairing_petersson_definite`.** For each cusp
   form $f$, this child states

   $$\mathcal B_n(f,f)=(2i)^n\langle f,f\rangle_{\mathrm{Pet}},\qquad
   \mathcal B_n(f,f)=0\Longleftrightarrow f=0.$$

   The pointwise identity underlying the normalization is

   $$B_n(L_z^n,L_{\bar z}^n)=(z-\bar z)^n=(2iy)^n.$$

   Convergence and positivity of the Petersson integral are part of the fourth obligation. Since
   $k=n+2$, its density relative to hyperbolic measure is $|f(z)|^2y^k$. Weight two is included,
   with $(2i)^0=1$.

Apply the third child with $q=g$ to obtain $\mathcal B_n(g,g)=0$, and with $q=v$ to obtain $\mathcal
B_n(v,v)=0$. The fourth child gives $g=v=0$, and the first gives $h=0$. These are exactly the
applications performed by the submitted Lean reduction. The four children remain open; the reduction
itself has no proof holes.

Reference: Columbia Spring 2021 modular-forms seminar notes, Week 4–5, §1.2, Theorem 1, pp. 7–10,
https://www.math.columbia.edu/~dmarcil/Seminars/2021_Spring/Notes/Week4-5.pdf. This decomposition
adapts its injectivity argument to the mission's reflected-summand and normalized cusp-primitive
conventions. The coefficientwise derivative and finite-coset integration interfaces are explicit
formalization choices.

<!-- Generated by add_prove2me_provenance.py -->
-/

section privateSection

noncomputable section
open scoped ComplexConjugate
open MTT.Cohomology

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (g h : CuspForm (MTT.GammaOne N) (k : ℤ)) (P : Binary ℂ)
    (hP : P ∈ MTT.Cohomology.Sym ℂ (k - 2))
    (hcob : ∀ γ : CongruenceSubgroup.Gamma1 N,
      cuspPrimitive g (cuspAct γ.val OnePoint.infty) +
        act !![-1, 0; 0, 1] (cuspPrimitive h
          (fractional !![-1, 0; 0, 1] (cuspAct γ.val OnePoint.infty))) =
      act γ.val.val P - P) :
    g = 0 ∧ h = 0 := by
  obtain ⟨v, hv, hvzero⟩ := period_reflected_cusp_form hN hk h
  obtain ⟨U, hU⟩ := principal_period_equivariant_primitive hN hk g h P hP hcob v hv
  have hp := equivariant_primitive_pairings_zero hN hk g v U hU
  have hgzero : g = 0 := (period_pairing_petersson_definite hN hk g).2.mp (hp g).1
  have hvzero' : v = 0 := (period_pairing_petersson_definite hN hk v).2.mp (hp v).2
  exact ⟨hgzero, hvzero.mp hvzero'⟩
end

end privateSection

public section publicSection

noncomputable section
open MTT.Cohomology
theorem MTT.Cohomology.period_cocycle_injective
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (g h : CuspForm (MTT.GammaOne N) (k : ℤ)) (P : Binary ℂ)
    (hP : P ∈ Sym ℂ (k - 2))
    (hcob : ∀ γ : CongruenceSubgroup.Gamma1 N,
      cuspPrimitive g (cuspAct γ.val OnePoint.infty) +
        act !![-1, 0; 0, 1] (cuspPrimitive h
          (fractional !![-1, 0; 0, 1] (cuspAct γ.val OnePoint.infty))) =
      act γ.val.val P - P) :
    g = 0 ∧ h = 0 := _root_.solution hN hk g h P hP hcob
end

end publicSection
