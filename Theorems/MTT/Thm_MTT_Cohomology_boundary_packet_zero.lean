/-
Based on Prove2Me node MTT.Cohomology.boundary_packet_zero
(fc2b6fc5-4f85-47be-904d-6e36aaa59d92) by cbirkbeck (2026-09-06).

Proof based on Prove2Me submission 7a6923f3-a211-4d85-86de-03356363bccf
by davidloeffler (2026-09-06); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import Definitions.MTT.Def_MTT_Cohomology_Boundary

import Theorems.MTT.Thm_MTT_Cohomology_boundary_hecke_scalar_at_one
import Theorems.MTT.Thm_MTT_cusp_log_weighted_square_summable
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# No boundary symbol carries the full eigenpacket of a cusp form

Theorem statement: `MTT.Cohomology.boundary_packet_zero` (`fc2b6fc5-4f85-47be-904d-6e36aaa59d92`),
by cbirkbeck, 2026-09-06.

Proof: submission `7a6923f3-a211-4d85-86de-03356363bccf`, by davidloeffler, 2026-09-06 (ACCEPTED);
locally adapted.

Let $f$ be a normalised cuspidal eigenform of weight $k\ge2$ on $\Gamma_1(N)$ with nebentypus
$\varepsilon$ and eigenvalues $a_\ell$ at every prime, and let $\Phi$ be a boundary datum whose
boundary cochain $\partial\Phi$ satisfies the nebentype law for $\varepsilon$ and

$$
T_\ell\,\partial\Phi=a_\ell\,\partial\Phi\qquad\text{for every prime }\ell .
$$

Then $\partial\Phi=0$.

This is the exclusion of boundary (Eisenstein) eigensystems from a cuspidal eigenpacket. A nonzero
boundary eigen-symbol has, at all but finitely many primes, eigenvalue
$\psi_1(\ell)+\psi_2(\ell)\ell^{k-1}$ for a pair of Dirichlet characters, so
$|a_\ell|\ge\ell^{k-1}-1$ at those primes. For $k\ge3$ this contradicts Hecke's bound $|a_\ell|\le
C\ell^{k/2}$. For every $k\ge2$, including weight $2$, an elementary mean-square argument suffices:
cuspidality gives $y^k|f(x+iy)|^2\le C_f$ on the upper half-plane, Parseval yields $\sum_{m\le
X}|a_m|^2\ll_f X^k$, hence $\sum_m|a_m|^2/m^{2k-1}<\infty$, whereas the boundary spectrum gives
$|a_\ell|^2/\ell^{2k-1}\ge1/(4\ell)$ at large primes, contradicting the divergence of
$\sum_\ell1/\ell$. No Ramanujan–Petersson bound is needed.

**Formalization Note** The eigenvalues $a_\ell$ are those of the cusp form `f.form`, tied to its
$q$-expansion by `f.coeff_eq` and `f.eigen`; the boundary spectrum is computed from the cusp
components of $\Phi$.

## Explanation of the source proof

# Boundary eigenpackets cannot be cuspidal

This gives the classical proof of the current statement of `MTT.Cohomology.boundary_packet_zero`.
The formal reduction assumes two open child lemmas: `MTT.Cohomology.boundary_hecke_scalar_at_one`
(Section 1) and `MTT.cusp_log_weighted_square_summable` (Section 2). Section 3 is checked in Lean
using Mathlib's divergence theorem. The mathematical arguments for the two children are supplied
below, but their Lean proofs remain to be completed.

Put $n=k-2$ and $B=\partial\Phi$, with exactly the convention in the published definition,
$B(x,y)=\Phi(y)-\Phi(x)$. We prove that $B=0$. In fact the separate nebentype hypothesis on $B$ is
unnecessary for this argument: only the Hecke eigenrelations at primes congruent to $1$ modulo $N$
are used.

## 1. The boundary Hecke calculation

Write a rational cusp as $[v]$, where $v=(a,c)^t$ is a primitive integral column, and write

$$L_v=aX+cY.$$

The stabilizer condition on the boundary datum implies

$$\Phi([v])=A(v)L_v^n$$

for a scalar $A(v)\in\mathbf C$. To see this, choose $\sigma\in\mathrm{SL}_2(\mathbf Z)$ with first
column $v$. The element $\sigma T^N\sigma^{-1}$ belongs to $\Gamma(N)\subseteq\Gamma_1(N)$ and fixes
$[v]$. Consequently $\operatorname{act}(\sigma^{-1})\Phi([v])$ is a homogeneous polynomial invariant
under $(X,Y)\mapsto(X,Y+NX)$. In characteristic zero such a polynomial is a multiple of $X^n$: set
$X=1$ and use that a polynomial invariant under translation by a nonzero constant is constant. This
also covers $n=0$.

Equivariance gives $A(\gamma v)=A(v)$ for $\gamma\in\Gamma_1(N)$, and $A(-v)=(-1)^nA(v)$ makes the
choice of primitive representative consistent.

We need the following elementary cusp fact. If primitive columns $v,w$ satisfy $w\equiv T^b v\pmod
N$, then $w=\gamma v$ for some $\gamma\in\Gamma_1(N)$. Indeed, first apply $T^b$ to reduce to
$v\equiv w$. Complete these columns to matrices $\sigma,\tau\in\mathrm{SL}_2(\mathbf Z)$. Modulo
$N$, the matrix $\tau^{-1}\sigma$ has first column $(1,0)^t$, hence is $T^t$ for some integer $t$
modulo $N$. Then $\tau T^t\sigma^{-1}\in\Gamma(N)$ sends $v$ to $w$.

Fix a prime $\ell\equiv1\pmod N$. Since $\varepsilon(\ell)=1$, the matrices in the existing Hecke
formula are

$$g_b=\begin{pmatrix}1&b\\0&\ell\end{pmatrix}\quad(0\le b<\ell),\qquad
 g_\infty=\begin{pmatrix}\ell&0\\0&1\end{pmatrix}.$$

For each matrix $g$, write $gv=d_gv_g$ with $v_g$ primitive and $d_g>0$. Since $\det g=\ell$, we
have $d_g\in\{1,\ell\}$. Moreover $d_g\equiv1\pmod N$. The reductions of the $g_b$ modulo $N$ are
$T^b$, and that of $g_\infty$ is the identity. The cusp fact therefore gives

$$A(v_g)=A(v).$$

The published slash operation uses the adjugate, so

$$
\operatorname{act}(\operatorname{adj}g)\Phi([gv])
 =A(v_g)L_{\operatorname{adj}(g)v_g}^{\,n}
 =A(v)\left(\frac\ell{d_g}\right)^nL_v^n.
$$

Exactly one of the $\ell+1$ values $d_g$ equals $\ell$. If $\ell\nmid c$, it is the unique $g_b$
with $a+bc\equiv0\pmod\ell$. If $\ell\mid c$, primitiveness gives $\ell\nmid a$, and it is
$g_\infty$. The other $\ell$ values are $1$. Thus, on boundary data,

$$\mathcal T_\ell\Phi=(1+\ell^{n+1})\Phi.$$

Taking differences commutes with every term in the Hecke operator. Hence the exact scalar identity
needed for the mission is

$$\boxed{T_\ell B=(1+\ell^{k-1})B\qquad(\ell\equiv1\pmod N).}$$

No diagonalization of the entire boundary space or classification of Eisenstein series is needed.

## 2. The cuspidal mean-square estimate

Let $a_m=\iota(f.\mathrm{coeff}(m))$, so these are the actual width-one Fourier coefficients by
`f.coeff_eq`. Cuspidality at every cusp and finite index imply a bound $y^k|f(x+iy)|^2\le C_f$ on
the upper half-plane. Parseval on a horizontal interval of length one gives

$$\sum_{m\ge1}|a_m|^2e^{-4\pi my}
 =\int_0^1|f(x+iy)|^2\,dx\le C_fy^{-k}.$$

Putting $y=1/X$ yields

$$\sum_{1\le m\le X}|a_m|^2\le C_fe^{4\pi}X^k.$$

This is the standard Parseval proof of the mean-square bound; see Rudnick, [Petersson formula
notes](https://www.math.tau.ac.il/~rudnick/courses/modular%20forms%202019/peterssonformula.pdf),
Lemma 1.1 and the proof of Theorem 1.2, pp. 2–3. For congruence level, the same argument uses
finitely many translates of a fundamental domain.

A dyadic decomposition now gives the slightly stronger summability statement useful with the
existing Mathlib prime theorem:

$$\boxed{\sum_{m\ge1}\frac{|a_m|^2\log m}{m^{k+1}}<\infty.}$$

Indeed the sum over $2^j\le m<2^{j+1}$ is bounded by a constant times $(j+1)2^{-j}$. This is
summable for every $k\ge2$.

## 3. Contradiction

If $B\ne0$, comparison with its assumed Hecke eigenrelation forces

$$a_\ell=1+\ell^{k-1}\qquad\text{for every prime }\ell\equiv1\pmod N.$$

Since $k\ge2$,

$$\frac{|a_\ell|^2\log\ell}{\ell^{k+1}}
 \ge\frac{\ell^{2k-2}\log\ell}{\ell^{k+1}}
 \ge\frac{\log\ell}{\ell}.$$

But

$$\sum_{\substack{\ell\ \mathrm{prime}\\\ell\equiv1\pmod N}}
 \frac{\log\ell}{\ell}=\infty.$$

This precise divergence statement is already in Mathlib as
`ArithmeticFunction.vonMangoldt.not_summable_residueClass_prime_div`, applied to the unit residue
class $1\in\mathbf Z/N\mathbf Z$. It contradicts the summability above. Thus $B=0$.

Weight $2$ needs no separate treatment. The contradiction uses the whole progression of primes,
rather than asserting that the elementary pointwise Hecke bound excludes one isolated eigenvalue
$1+\ell$.

<!-- Generated by add_prove2me_provenance.py -->
-/

section privateSection

noncomputable section
open scoped BigOperators
open MTT.Cohomology

private theorem close_boundary_packet
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (Φ : Cusp → Binary ℂ) (_hΦ : IsBoundaryDatum N (k-2) Φ)
    (hH : ∀ l : ℕ, l.Prime →
      primeHecke (ι (f.epsilon (l : ZMod N))) l (boundaryCochain Φ) =
        ι (f.coeff l) • boundaryCochain Φ)
    (hscalar : ∀ l : ℕ, l.Prime → (l : ZMod N) = 1 →
      primeHecke (1 : ℂ) l (boundaryCochain Φ) =
        ((1 + l^(k-1) : ℕ) : ℂ) • boundaryCochain Φ)
    (hsum : Summable fun m : ℕ =>
      ‖ι (f.coeff m)‖^2 * Real.log m / (m : ℝ)^(k+1)) :
    boundaryCochain Φ = 0 := by
  have : NeZero N := ⟨Nat.ne_of_gt hN⟩
  by_contra hne
  have heigen (l : ℕ) (hl : l.Prime) (hlN : (l : ZMod N) = 1) :
      ι (f.coeff l) = ((1 + l^(k-1) : ℕ) : ℂ) := by
    have h := hH l hl
    rw [hlN, map_one, map_one, hscalar l hl hlN] at h
    exact (smul_left_injective ℂ hne) h.symm
  apply ArithmeticFunction.vonMangoldt.not_summable_residueClass_prime_div
    (a := (1 : ZMod N)) isUnit_one
  apply Summable.of_nonneg_of_le _ _ hsum
  · intro m
    exact div_nonneg (by split_ifs; exact ArithmeticFunction.vonMangoldt.residueClass_nonneg _ _; rfl) (Nat.cast_nonneg _)
  · intro m
    by_cases hm : m.Prime
    · by_cases hmN : (m : ZMod N) = 1
      · simp only [hm, ite_true, ArithmeticFunction.vonMangoldt.residueClass,
          Set.indicator_apply, Set.mem_ofPred_eq, hmN, ite_true, ArithmeticFunction.vonMangoldt_apply_prime hm]
        rw [heigen m hm hmN, Complex.norm_natCast, Nat.cast_add, Nat.cast_one, Nat.cast_pow]
        have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm.pos
        have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.one_lt.le
        have hp : (m : ℝ)^k ≤ (1 + (m : ℝ)^(k-1))^2 := by
          calc
            (m : ℝ)^k ≤ (m : ℝ)^(2*(k-1)) := pow_le_pow_right₀ hm1 (by omega)
            _ = ((m : ℝ)^(k-1))^2 := by rw [mul_comm 2, pow_mul]
            _ ≤ (1 + (m : ℝ)^(k-1))^2 := by nlinarith [pow_nonneg hm0.le (k-1)]
        rw [div_le_div_iff₀ hm0 (pow_pos hm0 _), pow_succ]
        calc
          Real.log (m : ℝ) * ((m : ℝ)^k * m) = (m : ℝ)^k * Real.log m * m := by ring
          _ ≤ (1 + (m : ℝ)^(k-1))^2 * Real.log m * m := by gcongr
      · simp only [hm, ite_true, ArithmeticFunction.vonMangoldt.residueClass,
          Set.indicator_apply, Set.mem_ofPred_eq, hmN, ite_false, zero_div]
        exact div_nonneg (mul_nonneg (sq_nonneg _) (Real.log_nonneg (by exact_mod_cast hm.one_lt.le))) (pow_nonneg (Nat.cast_nonneg _) _)
    · simp only [hm, ite_false, zero_div]
      by_cases hm0 : m = 0
      · subst m; simp
      · exact div_nonneg (mul_nonneg (sq_nonneg _) (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm0))) (pow_nonneg (Nat.cast_nonneg _) _)

set_option linter.unusedVariables false in
theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (Φ : Cusp → Binary ℂ) (hΦ : IsBoundaryDatum N (k-2) Φ)
    (hlaw : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      boundaryCochain Φ (cuspAct γ.val x, cuspAct γ.val y) =
        ι (f.epsilon (γ.val 1 1 : ZMod N)) • act γ.val.val (boundaryCochain Φ (x, y)))
    (hH : ∀ l : ℕ, l.Prime →
      primeHecke (ι (f.epsilon (l : ZMod N))) l (boundaryCochain Φ) =
        ι (f.coeff l) • boundaryCochain Φ) :
    boundaryCochain Φ = 0  := by
  apply close_boundary_packet hN hk ι f Φ hΦ hH
  · intro l hl hlN
    have h := MTT.Cohomology.boundary_hecke_scalar_at_one hN Φ hΦ l hl hlN
    have hk' : k-2+1 = k-1 := by omega
    simpa only [hk'] using h
  · simpa only [f.coeff_eq] using MTT.cusp_log_weighted_square_summable hN hk f.form
end

end privateSection

public section publicSection

noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.boundary_packet_zero
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (Φ : Cusp → Binary ℂ) (hΦ : IsBoundaryDatum N (k-2) Φ)
    (hlaw : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      boundaryCochain Φ (cuspAct γ.val x, cuspAct γ.val y) =
        ι (f.epsilon (γ.val 1 1 : ZMod N)) • act γ.val.val (boundaryCochain Φ (x, y)))
    (hH : ∀ l : ℕ, l.Prime →
      primeHecke (ι (f.epsilon (l : ZMod N))) l (boundaryCochain Φ) =
        ι (f.coeff l) • boundaryCochain Φ) :
    boundaryCochain Φ = 0 := _root_.solution hN hk ι f Φ hΦ hlaw hH
end

end publicSection
