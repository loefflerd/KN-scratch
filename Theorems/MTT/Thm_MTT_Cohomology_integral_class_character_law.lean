/-
Based on Prove2Me node MTT.Cohomology.integral_class_character_law
(804bcccd-e8d1-4bbf-b71f-f57e0ec09044) by allychan327 (2026-09-06).

Proof based on Prove2Me submission 84e2ebb1-6a56-4547-be04-77c0959afc2b
by allychan327 (2026-09-07); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import Definitions.MTT.Def_MTT_Cohomology
public import Mathlib.RingTheory.Flat.Basic

import Theorems.MTT.Thm_MTT_Cohomology_integral_class_character_law_infty

/-!
# Nebentype law for the modular symbol of an eigenform

Theorem statement: `MTT.Cohomology.integral_class_character_law`
(`804bcccd-e8d1-4bbf-b71f-f57e0ec09044`), by allychan327, 2026-09-06.

Proof: submission `84e2ebb1-6a56-4547-be04-77c0959afc2b`, by allychan327, 2026-09-07 (ACCEPTED);
locally adapted.

Let $f$ be a normalized algebraic cuspidal Hecke eigenform of weight $k \ge 2$ and level $N > 0$,
with nebentypus $\varepsilon$, so that for every
$\gamma=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\Gamma_0(N)$
$$f(\gamma z)=\varepsilon(d)\,(cz+d)^{k}\,f(z).$$
Let $\varphi$ be a compactly supported cohomology class of weight $n=k-2$ whose coefficient
functionals
compute the modular integrals of $f$, that is
$$\bigl\langle \varphi([\infty]-[r]),\ X^{j}Y^{\,k-2-j}\bigr\rangle
= \binom{k-2}{j}\,\int_{r}^{i\infty} f(z)\,z^{j}\,dz \quad (0\le j\le k-2,\ r\in\mathbf Q),$$
in the normalization fixed by `IntegralClass`. Then $\varphi$ obeys the corresponding nebentype law
in cohomology: for every $\gamma\in\Gamma_0(N)$ and all cusps $x,y$,
$$\varphi(\gamma x,\gamma y)=\varepsilon(d)\cdot\bigl(\gamma\cdot\varphi(x,y)\bigr),$$
where $\gamma$ acts on binary forms of degree $k-2$ by $P(X,Y)\mapsto P\bigl((X,Y)\gamma\bigr)$ and
$\varepsilon(d)$ is transported to $\mathbf C$ along the fixed embedding $\iota$.

The class $\varphi$ is determined by the displayed integrals: the values on the paths $[\infty]-[r]$
determine all values by the cocycle relation, and a binary form of degree $k-2$ is determined by its
$k-1$ coefficients. So the statement is not an extra axiom but a *theorem* about the modular
integral —
and it is exactly the point where analysis enters. Proving it requires the transformation behaviour
of
the path integral $\int_{r}^{i\infty}f(z)P(z)\,dz$ under $z \mapsto \gamma z$: the substitution
turns the vertical ray into a circular arc, so the identity rests on the holomorphy of $f$ and the
homotopy invariance of contour integrals in the upper half-plane, together with the rapid decay of a
cusp form at the cusps.

This is the standard bridge from the automorphy of $f$ to the $\Gamma_0(N)$-equivariance of its
modular
symbol, and it is what upgrades a class satisfying only the Hecke relations to a full eigenpacket.

## Explanation of the source proof

# The nebentypus law only has to be checked on paths from $\infty$

## What is being reduced

Let $f$ be a normalized algebraic cuspidal eigenform of level $N$ and weight $k$, with nebentypus
$\varepsilon$, and let
$$\varphi\in H^1_c\bigl(\Gamma_1(N),\operatorname{Sym}^{k-2}\mathbf C^2\bigr)$$
be analytically normalised for $f$, i.e.
$\operatorname{ev}_{j,r}(\varphi)=\binom{k-2}{j}\int_{r}^{i\infty}f\,z^{j}\,dz$ for $0\le j\le k-2$
and $r\in\mathbf Q$. The nebentypus law asserts that $\varphi$, which is by construction only
$\Gamma_1(N)$-equivariant, is in fact $\Gamma_0(N)$-equivariant up to the character: for every
$\gamma=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\Gamma_0(N)$ and all cusps $x,y$,
$$\varphi(\gamma x,\gamma y)\;=\;\varepsilon(d)\cdot\gamma\!\cdot\!\varphi(x,y).$$

The claim here is that it suffices to verify this for $x=[\infty]$ and $y=[r]$ with $r$ rational.
Everything else is formal.

## The argument

Write
$$F(x,y)\;=\;\varphi(\gamma x,\gamma y)-\varepsilon(d)\cdot\gamma\!\cdot\!\varphi(x,y),$$
so the goal is $F\equiv 0$. Both terms are cocycles in $(x,y)$: the first because
$(x,y)\mapsto(\gamma x,\gamma y)$ is induced by an action on cusps, the second because the
coefficient action $\gamma\cdot(-)$ is linear and so preserves the relation
$\varphi(x,y)+\varphi(y,z)=\varphi(x,z)$. Hence $F$ is a cocycle, and two consequences follow
immediately.

**The diagonal vanishes.** Putting $x=y=z$ in the cocycle relation for $\varphi$ gives
$\varphi(x,x)+\varphi(x,x)=\varphi(x,x)$, hence $\varphi(x,x)=0$; this is `diag_zero`. Applying it
to both terms gives $F(x,x)=0$, and in particular $F([\infty],[\infty])=0$.

**Everything decomposes through $\infty$.** The cocycle relation with base point $[\infty]$ gives
$\varphi(x,y)=\varphi([\infty],y)-\varphi([\infty],x)$, which is `val_sub`; the same identity holds
for $\varphi(\gamma\cdot,\gamma\cdot)$ with base point $\gamma[\infty]$. So
$$F(x,y)\;=\;F([\infty],y)-F([\infty],x).$$

Since $\mathbf P^1(\mathbf Q)=\mathbf Q\cup\{\infty\}$, the values $F([\infty],v)$ are covered by
two cases: $v=[\infty]$, handled by the diagonal, and $v=[r]$ with $r\in\mathbf Q$, which is exactly
the hypothesis `integral_class_character_law_infty`. So $F([\infty],v)=0$ for every cusp $v$, and
therefore $F\equiv 0$.

In Lean this is the `key` step — an induction on the one-point compactification, whose two branches
are `diag_zero` and the imported node — followed by a single rewrite chain that turns both sides
into the difference of their values on paths from $\infty$, using `val_sub`, linearity of the
coefficient action (`map_sub`) and `smul_sub`.

## Why this is the right place to cut

Notice what the argument does *not* use: no equivariance property of $\varphi$, no homogeneity of
its values, no property of $f$. It is pure cocycle bookkeeping, and correspondingly it is the half
of the statement that a formalisation can dispatch mechanically.

What remains is genuinely analytic and is now stated in its minimal form. On a path from $\infty$ to
$r$, the normalisation hypothesis makes $\varphi([\infty],[r])$ explicitly the period polynomial
$$\sum_{j=0}^{k-2}\binom{k-2}{j}\Bigl(\int_{r}^{i\infty}f\,z^{j}\,dz\Bigr)X^{j}Y^{\,k-2-j},$$
so the imported node says precisely that this period polynomial transforms under $\Gamma_0(N)$ by
$\varepsilon(d)$ times the coefficient action — the classical transformation law. Its proof has to
compare the integral of $f$ along the vertical ray above $r$ with the integral along the image of
that ray under $\gamma$, which is a circular arc through $\gamma r$ and $\gamma\infty$ rather than a
ray. That comparison is a contour deformation, legitimate because $f$ is holomorphic on the upper
half-plane and decays at the cusps, and it is not available from the automorphy of $f$ alone.
Isolating it is the point of the split.

<!-- Generated by add_prove2me_provenance.py -->
-/

section privateSection

set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

namespace P2MCL

variable {N n : ℕ} {R : Type*} [CommRing R]

/-- The cocycle relation at a constant triple forces the diagonal to vanish. -/
theorem diag_zero (φ : Hc N n R) (z : Cusp) : φ.val (z, z) = 0 := by
  have h := φ.2.2.1 z z z
  have h2 : φ.val (z, z) + φ.val (z, z) - φ.val (z, z) = 0 := by rw [h]; simp
  simpa using h2

/-- Every path decomposes through any fixed base cusp. -/
theorem val_sub (φ : Hc N n R) (c a b : Cusp) :
    φ.val (a, b) = φ.val (c, b) - φ.val (c, a) := by
  have h := φ.2.2.1 c a b
  rw [← h]; ring

end P2MCL

open P2MCL in
theorem solution {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (φ : Hc N (k-2) ℂ) (hφ : IntegralClass f.form φ)
    (γ : CongruenceSubgroup.Gamma0 N) (x y : Cusp) :
    φ.val (cuspAct γ.val x, cuspAct γ.val y)
      = ι (f.epsilon (γ.val 1 1 : ZMod N)) • act γ.val.val (φ.val (x, y)) := by
  have key : ∀ v : Cusp,
      φ.val (cuspAct γ.val OnePoint.infty, cuspAct γ.val v)
        = ι (f.epsilon (γ.val 1 1 : ZMod N)) • act γ.val.val (φ.val (OnePoint.infty, v)) := by
    intro v
    induction v using OnePoint.rec with
    | infty => rw [diag_zero, diag_zero, map_zero, smul_zero]
    | coe r =>
        exact MTT.Cohomology.integral_class_character_law_infty hN hk ι f φ hφ γ r
  rw [val_sub φ (cuspAct γ.val OnePoint.infty) (cuspAct γ.val x) (cuspAct γ.val y),
      key y, key x, val_sub φ OnePoint.infty x y, map_sub, smul_sub]
end

end privateSection

public section publicSection

noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.integral_class_character_law
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (φ : Hc N (k-2) ℂ) (hφ : IntegralClass f.form φ)
    (γ : CongruenceSubgroup.Gamma0 N) (x y : Cusp) :
    φ.val (cuspAct γ.val x, cuspAct γ.val y)
      = ι (f.epsilon (γ.val 1 1 : ZMod N)) • act γ.val.val (φ.val (x, y)) := _root_.solution hN hk ι f φ hφ γ x y
end

end publicSection
