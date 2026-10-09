/-
Based on Prove2Me node MTT.Cohomology.manin_generation
(f50f29b0-b8d5-4756-85c1-837165aeecdd) by allychan327 (2026-09-06).

Proof based on Prove2Me submission 64b4e938-c84d-4864-832b-4817742440ec
by allychan327 (2026-09-06); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import Definitions.MTT.Def_MTT_Cohomology
public import Mathlib.RingTheory.Flat.Basic

/-!
# Unimodular paths generate: vanishing criterion for modular symbols

Theorem statement: `MTT.Cohomology.manin_generation` (`f50f29b0-b8d5-4756-85c1-837165aeecdd`), by
allychan327, 2026-09-06.

Proof: submission `64b4e938-c84d-4864-832b-4817742440ec`, by allychan327, 2026-09-06 (ACCEPTED);
locally adapted.

Let $N, n \ge 0$ and let $R$ be any commutative ring. A compactly supported cohomology class
$\varphi \in H^1_c(\Gamma_1(N), \operatorname{Sym}^n R^2)$, realized concretely as a
$\Gamma_1(N)$-equivariant
cocycle $(x,y) \mapsto \varphi(x,y)$ on pairs of cusps, is determined by its values on the
**unimodular paths**.

Precisely: if $\varphi(g\cdot 0,\ g\cdot\infty) = 0$ for every $g \in SL_2(\mathbf{Z})$, then
$\varphi = 0$.

Dually this is the assertion that the degree-zero divisor group
$\operatorname{Div}^0(\mathbf{P}^1(\mathbf{Q}))$
is generated, as an abelian group, by the unimodular divisors $\{g\cdot\infty\} - \{g\cdot 0\}$ with
$g \in SL_2(\mathbf{Z})$.
This is the *generation* half of Manin's theorem on modular symbols, and it is proved by the
continued-fraction
algorithm: given a fraction $p/q$ in lowest terms with $q > 0$, Bézout's identity supplies integers
$p', q'$ with
$$p q' - p' q = 1, \qquad 0 \le q' < q,$$
so that $\begin{pmatrix} p & p' \\ q & q'\end{pmatrix} \in SL_2(\mathbf{Z})$ carries the path
$\{0,\infty\}$ to
$\{p'/q',\ p/q\}$. The cocycle relation $\varphi(x,y) + \varphi(y,z) = \varphi(x,z)$ then replaces
the path
$(\infty, p/q)$ by $(\infty, p'/q')$, whose denominator is strictly smaller, and the induction
terminates.

The hypothesis is imposed for all of $SL_2(\mathbf{Z})$, not merely for a set of coset
representatives; the
reduction to finitely many cosets is a separate step supplied by $\Gamma_1(N)$-equivariance. The
statement holds
over an arbitrary coefficient ring $R$ because the argument uses only the cocycle relation and never
the
coefficients; this generality is exactly what is needed for base-change arguments.

## Explanation of the source proof

## Manin's continued-fraction trick

Write $\varphi$ for the given class, viewed as a $\Gamma_1(N)$-equivariant cocycle on pairs of
cusps with values in $\operatorname{Sym}^n R^2$, and assume $\varphi(g\cdot 0, g\cdot\infty)=0$
for every $g\in SL_2(\mathbf Z)$. Only two of the three defining properties are used: the cocycle
relation
$$\varphi(x,y)+\varphi(y,z)=\varphi(x,z),$$
and nothing at all about the coefficient ring $R$.

**Step 1: normal forms for the two cusps moved by a matrix.**
For $g=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in SL_2(\mathbf Z)$ acting on $\mathbf P^1(\mathbf Q)$,
$$g\cdot\infty=\begin{cases}\infty,&c=0\\ a/c,&c\neq0\end{cases}
\qquad
g\cdot 0=\begin{cases}\infty,&d=0\\ b/d,&d\neq0.\end{cases}$$
These are read off from the projective-line action; the action is a genuine group action, so
$(gh)\cdot x=g\cdot(h\cdot x)$.

**Step 2: the descent.**
Let $p/q$ be a fraction with $q>0$ and $\gcd(p,q)=1$. Bézout gives $u,v$ with $up+vq=1$. Put
$$q'=u\bmod q,\qquad p'=-\bigl(v+p\lfloor u/q\rfloor\bigr),$$
so that $pq'-p'q=1$ and $0\le q'<q$. Hence
$g=\begin{pmatrix}p&p'\\q&q'\end{pmatrix}\in SL_2(\mathbf Z)$, and by Step 1
$$g\cdot\infty=p/q,\qquad g\cdot 0=\begin{cases}\infty,&q'=0\\ p'/q',&q'\neq0.\end{cases}$$
The hypothesis says $\varphi(g\cdot 0,\ p/q)=0$. If $q'=0$ this is literally
$\varphi(\infty,p/q)=0$ and we are done. Otherwise $\varphi(p'/q',\ p/q)=0$, and the cocycle
relation
$$\varphi(\infty,p'/q')+\varphi(p'/q',p/q)=\varphi(\infty,p/q)$$
reduces the claim for $p/q$ to the claim for $p'/q'$, whose denominator $q'$ is *strictly smaller*.
Strong induction on the bound for the denominator therefore gives $\varphi(\infty,p/q)=0$ for every
reduced $p/q$ with $q>0$. Note that the induction is carried out on the pair of integers $(p,q)$
rather than on the reduced form of a rational number; the coprimality of $(p',q')$ is immediate
from $pq'-p'q=1$.

**Step 3: from $(\infty,r)$ to arbitrary pairs.**
Every rational $r$ is $r.\mathrm{num}/r.\mathrm{den}$ in lowest terms with positive denominator, so
$\varphi(\infty,x)=0$ for all $x\in\mathbf P^1(\mathbf Q)$ — the case $x=\infty$ being
$\varphi(x,x)=0$, itself a consequence of the cocycle relation. Two further consequences of that
relation, $\varphi(x,x)=0$ and $\varphi(y,x)=-\varphi(x,y)$, then give for arbitrary $x,y$
$$\varphi(x,y)=\varphi(x,\infty)+\varphi(\infty,y)=-\varphi(\infty,x)+\varphi(\infty,y)=0 .$$
Hence $\varphi=0$. $\square$

Dually the statement says that $\operatorname{Div}^0(\mathbf P^1(\mathbf Q))$ is generated as an
abelian group by the unimodular divisors $\{g\cdot\infty\}-\{g\cdot 0\}$; this is the generation
half of Manin's theorem. It holds over any coefficient ring because no coefficient is ever
divided, and it is the form needed for base-change arguments, where the coefficients are an
arbitrary flat $\mathbf Z$-algebra.

<!-- Generated by add_prove2me_provenance.py -->
-/

section privateSection

set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
open MTT.Cohomology

namespace P2MMG

open MvPolynomial

abbrev SL2 := Matrix.SpecialLinearGroup (Fin 2) ℤ

/-! ### The action of `SL(2,ℤ)` on the cusps, in coordinates -/

theorem cuspAct_infty (g : SL2) :
    cuspAct g OnePoint.infty
      = if (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 then OnePoint.infty
        else ((((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℚ)
              / ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℚ)) : ℚ) := by
  rw [cuspAct, OnePoint.smul_infty_eq_ite]
  simp [Matrix.SpecialLinearGroup.mapGL]

theorem cuspAct_zero (g : SL2) :
    cuspAct g ((0 : ℚ) : Cusp)
      = if (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 0 then OnePoint.infty
        else ((((g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℚ)
              / ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℚ)) : ℚ) := by
  rw [cuspAct, OnePoint.smul_some_eq_ite]
  simp [Matrix.SpecialLinearGroup.mapGL]

theorem cuspAct_mul (g h : SL2) (x : Cusp) :
    cuspAct (g * h) x = cuspAct g (cuspAct h x) := by
  simp [cuspAct, map_mul, mul_smul]

/-! ### Elementary consequences of the cocycle relation -/

variable {N n : ℕ} {R : Type*} [CommRing R]

theorem hc_add (φ : Hc N n R) (x y z : Cusp) :
    φ.val (x, y) + φ.val (y, z) = φ.val (x, z) := φ.2.2.1 x y z

theorem hc_hom (φ : Hc N n R) (x y : Cusp) : φ.val (x, y) ∈ MTT.Cohomology.Sym R n := φ.2.1 x y

theorem hc_equiv (φ : Hc N n R) (γ : CongruenceSubgroup.Gamma1 N) (x y : Cusp) :
    φ.val (cuspAct γ.val x, cuspAct γ.val y) = act γ.val.val (φ.val (x, y)) :=
  φ.2.2.2 γ x y

theorem hc_self (φ : Hc N n R) (x : Cusp) : φ.val (x, x) = 0 := by
  have h := hc_add φ x x x
  have h2 : φ.val (x, x) + φ.val (x, x) = 0 + φ.val (x, x) := by rw [zero_add]; exact h
  exact add_right_cancel h2

theorem hc_swap (φ : Hc N n R) (x y : Cusp) : φ.val (y, x) = -φ.val (x, y) := by
  have h : φ.val (x, y) + φ.val (y, x) = 0 := by rw [hc_add φ x y x, hc_self]
  have h2 : φ.val (x, y) + φ.val (y, x) - φ.val (x, y) = 0 - φ.val (x, y) := by rw [h]
  simpa [add_sub_cancel_left] using h2

end P2MMG

namespace P2MMG

open MvPolynomial

variable {N n : ℕ} {R : Type*} [CommRing R]

/-- Manin's trick. If `φ` kills every unimodular path `(g·0, g·∞)`, it kills every
path `(∞, p/q)`; the induction is on the denominator. -/
theorem manin_aux (φ : Hc N n R)
    (hU : ∀ g : SL2, φ.val (cuspAct g ((0 : ℚ) : Cusp), cuspAct g OnePoint.infty) = 0) :
    ∀ (m : ℕ) (p q : ℤ), 0 < q → q ≤ (m : ℤ) → IsCoprime p q →
      φ.val (OnePoint.infty, (((p : ℚ) / (q : ℚ)) : Cusp)) = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro p q hq hqm hcop
    obtain ⟨u, v, huv⟩ := hcop
    set q' : ℤ := u % q with hq'def
    set p' : ℤ := -(v + p * (u / q)) with hp'def
    have hdet : p * q' - p' * q = 1 := by
      rw [hq'def, hp'def, Int.emod_def]
      linear_combination huv
    have hMdet : (!![p, p'; q, q'] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
      rw [Matrix.det_fin_two_of]; exact hdet
    set g : SL2 := ⟨!![p, p'; q, q'], hMdet⟩ with hgdef
    have hg00 : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = p := by simp [hgdef]
    have hg01 : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = p' := by simp [hgdef]
    have hg10 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = q := by simp [hgdef]
    have hg11 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = q' := by simp [hgdef]
    have hU' := hU g
    rw [cuspAct_infty, hg10, hg00, ite_eq_right hq.ne', cuspAct_zero, hg11, hg01] at hU'
    by_cases hq'0 : q' = 0
    · rw [ite_eq_left hq'0] at hU'
      exact hU'
    · rw [ite_eq_right hq'0] at hU'
      have hq'pos : 0 < q' := lt_of_le_of_ne (Int.emod_nonneg u hq.ne') (Ne.symm hq'0)
      have hq'lt : q' < q := Int.emod_lt_of_pos u hq
      have hcop' : IsCoprime p' q' := ⟨-q, p, by linear_combination hdet⟩
      have hrec : φ.val (OnePoint.infty, (((p' : ℚ) / (q' : ℚ)) : Cusp)) = 0 := by
        refine ih q'.toNat (by omega) p' q' hq'pos ?_ hcop'
        omega
      have hsum := hc_add φ OnePoint.infty (((p' : ℚ) / (q' : ℚ)) : Cusp)
        (((p : ℚ) / (q : ℚ)) : Cusp)
      rw [hrec, hU', zero_add] at hsum
      exact hsum.symm

theorem manin (φ : Hc N n R)
    (hU : ∀ g : SL2, φ.val (cuspAct g ((0 : ℚ) : Cusp), cuspAct g OnePoint.infty) = 0)
    (r : ℚ) : φ.val (OnePoint.infty, (r : Cusp)) = 0 := by
  have hcop : IsCoprime r.num (r.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd] using r.reduced
  have h := manin_aux φ hU r.den r.num (r.den : ℤ)
    (by exact_mod_cast r.pos) le_rfl hcop
  have hcast : (((r.den : ℤ) : ℚ)) = (r.den : ℚ) := by push_cast; ring
  rw [hcast, Rat.num_div_den] at h
  exact h

/-- A class killed on all unimodular paths is zero. -/
theorem hc_eq_zero_of_unimodular (φ : Hc N n R)
    (hU : ∀ g : SL2, φ.val (cuspAct g ((0 : ℚ) : Cusp), cuspAct g OnePoint.infty) = 0) :
    φ = 0 := by
  have hinf : ∀ x : Cusp, φ.val (OnePoint.infty, x) = 0 := by
    intro x
    induction x using OnePoint.rec with
    | infty => exact hc_self φ _
    | coe r => exact manin φ hU r
  refine Subtype.ext (funext fun D => ?_)
  have hsum := hc_add φ D.1 OnePoint.infty D.2
  rw [hinf D.2, add_zero] at hsum
  have : φ.val (D.1, OnePoint.infty) = 0 := by
    rw [hc_swap φ OnePoint.infty D.1, hinf D.1, neg_zero]
  rw [this] at hsum
  simpa using hsum.symm

end P2MMG

open P2MMG in
/-- Manin: the unimodular paths generate `Div⁰(P¹(ℚ))`, so a class killing all of them is zero. -/
theorem solution {N n : ℕ} {R : Type*} [CommRing R] (φ : Hc N n R)
    (hU : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      φ.val (cuspAct g ((0 : ℚ) : Cusp), cuspAct g OnePoint.infty) = 0) :
    φ = 0 :=
  hc_eq_zero_of_unimodular φ hU
end

end privateSection

public section publicSection

noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.manin_generation
    {N n : ℕ} {R : Type*} [CommRing R] (φ : Hc N n R)
    (hU : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      φ.val (cuspAct g ((0 : ℚ) : Cusp), cuspAct g OnePoint.infty) = 0) :
    φ = 0 := _root_.solution φ hU
end

end publicSection
