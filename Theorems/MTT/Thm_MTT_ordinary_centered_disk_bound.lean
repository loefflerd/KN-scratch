/-
Based on Prove2Me node MTT.ordinary_centered_disk_bound
(d678f59b-8280-4868-b9ab-84d81752bb5b) by davidloeffler (2026-09-06).

Proof based on Prove2Me submission cbc0ed70-d656-4035-966d-af98d8975557
by allychan327 (2026-09-06); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import Definitions.MTT.Def_MTT_Measures

import Mathlib.Analysis.Normed.Field.Instances

/-!
# Ordinary centred disk-moment bound in every critical degree

Theorem statement: `MTT.ordinary_centered_disk_bound` (`d678f59b-8280-4868-b9ab-84d81752bb5b`), by
davidloeffler, 2026-09-06.

Proof: submission `cbc0ed70-d656-4035-966d-af98d8975557`, by allychan327, 2026-09-06 (ACCEPTED);
locally adapted.

Fix a prime $p$, a positive level $N$, and a weight $k\ge2$. Let $f$ be a normalized algebraic
cuspidal Hecke eigenform, with fixed embeddings into $\mathbf C$ and $\mathbf C_p$, a signed period
system $P$ with finitely generated integral lattice, and an ordinary root $\alpha$ of its Hecke
polynomial.

Write $M_{s,t}(n,a)$ for the signed degree-$t$ disk moment defined by MTT (10.2), and define its
centred degree-$j$ moment by
$$M^{\mathrm{cent}}_{s,j}(n,a)=\sum_{t=0}^j\binom jt(-a)^{j-t}M_{s,t}(n,a).$$
There exists a real constant $C\ge0$, independent of the sign $s$, depth $n\ge1$, integer centre
$a$, and degree $0\le j\le k-2$, such that
$$\left|M^{\mathrm{cent}}_{s,j}(n,a)\right|_p\le C p^{-nj}.$$

This is the slope-zero centred-moment estimate in MTT I.§11. Its degree-zero case bounds disk
masses, while the positive-degree decay controls polynomial approximation on shrinking disks. It is
the bound needed to recover all critical polynomial moments when extending the distribution to a
bounded measure.

**Formalization Note** The left side is expressed directly as a binomial sum of the existing disk
moments, without assuming a measure already exists. The right side uses the norm of $p^{nj}$ in
$\mathbf C_p$.

## Explanation of the source proof

## Statement

Fix a prime $p$, a level $N\ge 1$, a weight $k\ge 2$, embeddings $\iota:\overline{\mathbf
Q}\to\mathbf C$ and $\iota_p:\overline{\mathbf Q}\to\mathbf C_p$, a normalized algebraic cuspidal
Hecke eigenform $f$, a signed period system $P$ for $f$, and an ordinary root $\alpha$ of the Hecke
polynomial of $f$ at $p$. Writing $M_{s,t}(n,a)$ for the disk moment of MTT (10.2), we prove

$$\exists\,C\ge 0\ \ \forall s\in\{\pm\},\ \forall n\ge 1,\ \forall a\in\mathbf Z,\ \forall\, 0\le
j\le k-2:\qquad
\Bigl\|\sum_{t=0}^{j}\binom jt(-a)^{j-t}M_{s,t}(n,a)\Bigr\|_p\ \le\ C\,\bigl\|p^{nj}\bigr\|_p .$$

The argument uses exactly two of the available hypotheses: the normalization $\|\alpha\|_p=1$
contained in `IsOrdinaryRoot`, and the finite generation of the $\mathbf Z$-lattice of normalized
signed modular-symbol values recorded in the `Periods` structure. The Hecke eigenvalue relation, the
character law, and the complex comparison isomorphism are not needed.

## Proof idea

The disk moments are built from the algebraic modular symbols

$$A_t(a,m)\;=\;\sum_{u=0}^{t}\binom tu m^{u}a^{t-u}\,P_{s,u}(-a/m),$$

which is the substitution $X\mapsto mX+a$ applied to the sequence $(P_{s,u})_u$ of normalized signed
values. Recentring at $a$ inverts that substitution exactly. Binomial inversion is not an estimate
but an identity: every term of degree $<j$ cancels, and only the top term survives, with the factor
$m^{j}$ in front. Since $m=p^{n}$ (respectively $p^{n-1}$ for the correction term of (10.2)), that
factor *is* the asserted decay $p^{-nj}$, and the single surviving coefficient is $p$-adically
bounded because it lies in a finitely generated $\mathbf Z$-module.

So the estimate is really a cancellation followed by an integrality statement, and both of the two
hypotheses used enter only to keep the prefactors of size $\le 1$.

## Step 1: binomial inversion

Let $R$ be a commutative ring, $V:\mathbf N\to R$ a sequence, and $m,a\in R$. Then for every $j$,

$$\sum_{t=0}^{j}\binom jt(-a)^{j-t}\sum_{u=0}^{t}\binom tu m^{u}a^{t-u}V_u\;=\;m^{j}V_j .$$

Exchanging the two summations puts the left side in the form $\sum_{u=0}^{j}m^{u}V_u\,S_{j,u}$ with

$$S_{j,u}=\sum_{t=u}^{j}\binom jt\binom tu(-a)^{j-t}a^{t-u}.$$

The subset-of-a-subset identity $\binom jt\binom tu=\binom ju\binom{j-u}{t-u}$ and the substitution
$t=u+v$ turn this into

$$S_{j,u}=\binom ju\sum_{v=0}^{j-u}\binom{j-u}{v}a^{v}(-a)^{(j-u)-v}=\binom
ju\bigl(a+(-a)\bigr)^{j-u}=\binom ju\,0^{\,j-u},$$

by the binomial theorem. For $u\le j$ the factor $0^{\,j-u}$ vanishes unless $u=j$, so only the term
$u=j$ survives and it equals $m^{j}V_j$. This is `centered_collapse` in the submission, and it is
where the whole cancellation happens.

## Step 2: the lattice bound

Let $S\subseteq\overline{\mathbf Q}$ be a set whose $\mathbf Z$-span is finitely generated, say by a
finite set $T$. Put

$$B=\sum_{t\in T}\|\iota_p(t)\|_p .$$

Then $\|\iota_p(x)\|_p\le B$ for every $x\in S$. Indeed, $\iota_p$ is a ring homomorphism, hence
$\mathbf Z$-linear, and the claim propagates along the generation of $\mathbf Z\text{-span}(T)$: it
holds on generators because each summand of $B$ is nonnegative; it is preserved under addition
because $\mathbf C_p$ is ultrametric, $\|x+y\|_p\le\max(\|x\|_p,\|y\|_p)$; and it is preserved under
multiplication by $c\in\mathbf Z$ because $\|c\|_p\le 1$ in $\mathbf C_p$. The ultrametric
inequality is essential here — the triangle inequality alone gives nothing, since the integer
coefficients are unbounded.

Applying this to the set $\{P_{s,j}(r): s,\ r\in\mathbf Q,\ 0\le j\le k-2\}$, whose $\mathbf Z$-span
is finitely generated by hypothesis, produces a constant $B\ge 0$ with

$$\|\iota_p(P_{s,j}(r))\|_p\le B\qquad\text{for all }s,\ r,\text{ and }0\le j\le k-2 .$$

The same $B$ serves both signs, all centres, all depths, and all admissible degrees; this uniformity
is what makes the final constant independent of $(s,n,a,j)$.

## Step 3: collapsing the centred moment

By definition,

$$M_{s,t}(n,a)=\alpha^{-n}\,\iota_p
A_t\bigl(a,p^{n}\bigr)-\frac{\iota_p(\varepsilon(p))\,p^{k-2}}{\alpha^{n+1}}\;\iota_p
A_t\bigl(a,p^{n-1}\bigr).$$

Both occurrences of $A_t$ are $R$-linear images of the same shape treated in Step 1, with $R=\mathbf
C_p$, $V_u=\iota_p\bigl(P_{s,u}(-a/m)\bigr)$, and $m$ equal to $p^{n}$ or $p^{n-1}$. Splitting the
centred sum along the difference and applying Step 1 to each half gives the closed form

$$\sum_{t=0}^{j}\binom jt(-a)^{j-t}M_{s,t}(n,a)
=\frac{p^{nj}}{\alpha^{n}}\,\iota_p\Bigl(P_{s,j}\bigl(-a/p^{n}\bigr)\Bigr)
-\frac{\iota_p(\varepsilon(p))\,p^{k-2}}{\alpha^{n+1}}\,p^{(n-1)j}\,\iota_p\Bigl(P_{s,j}\bigl(-a/p^{n-1}\bigr)\Bigr).$$

Every modular symbol of degree $<j$ has disappeared; two algebraic values remain.

## Step 4: the estimate

Write $q=\|p\|_p\le 1$ and $E=\|\iota_p(\varepsilon(p))\|_p$. Since $\|\alpha\|_p=1$, we have
$\|\alpha^{-n}\|_p=\|\alpha^{-(n+1)}\|_p=1$, so the two terms of Step 3 are bounded by

$$q^{nj}\,B\qquad\text{and}\qquad E\,q^{\,(k-2)+(n-1)j}\,B$$

respectively, using Step 2 for the two algebraic values. For $n\ge 1$ and $0\le j\le k-2$ one has
$nj=(n-1)j+j\le (k-2)+(n-1)j$, and $q\le 1$ makes $t\mapsto q^{t}$ nonincreasing, so the second
bound is at most $E\,B\,q^{nj}$. The triangle inequality then gives

$$\Bigl\|\sum_{t=0}^{j}\binom jt(-a)^{j-t}M_{s,t}(n,a)\Bigr\|_p\le
(B+EB)\,q^{nj}=(B+EB)\,\bigl\|p^{nj}\bigr\|_p .$$

Thus $C=B+EB$ works, and it depends only on $f,\iota_p,P,\alpha,p,k$ — not on the sign, the depth,
the centre, or the degree. This is the constant produced by the submission.

## Remarks

The degree-zero case $j=0$ of the conclusion is the boundedness of the disk masses,
$\|M_{s,0}(n,a)\|_p\le C$, which is the slope-zero statement that a bounded measure exists at all;
the positive-degree cases give the decay $O(p^{-nj})$ on shrinking disks that controls polynomial
approximation. Together they are precisely the input needed to extend the distribution to a bounded
$\mathbf C_p$-valued measure on $\mathbf Z_p^{\times}$.

The hypothesis $\|\alpha\|_p=1$ cannot be dropped: for a root of positive slope $v(\alpha)=h>0$ the
factor $\alpha^{-n}$ contributes $p^{nh}$ and the bound degrades to $O(p^{-n(j-h)})$, which is the
reason the general (non-ordinary) case of MTT I.§11 produces an unbounded, merely $h$-admissible
distribution rather than a measure.

<!-- Generated by add_prove2me_provenance.py -->
-/

section privateSection

noncomputable section
open Finset MTT

namespace MTTCentred

/-- Binomial inversion: recentring the shifted moments at `a` recovers `m ^ j * V j`. -/
theorem centered_collapse {R : Type*} [CommRing R] (V : ℕ → R) (m a : R) (j : ℕ) :
    (∑ t ∈ range (j + 1), (j.choose t : R) * (-a) ^ (j - t) *
      (∑ u ∈ range (t + 1), (t.choose u : R) * m ^ u * a ^ (t - u) * V u))
      = m ^ j * V j := by
  have step1 : ∀ t ∈ range (j + 1),
      (j.choose t : R) * (-a) ^ (j - t) *
        (∑ u ∈ range (t + 1), (t.choose u : R) * m ^ u * a ^ (t - u) * V u)
      = ∑ u ∈ range (t + 1),
          ((j.choose t : R) * (t.choose u : R)) *
            ((-a) ^ (j - t) * a ^ (t - u) * m ^ u * V u) := by
    intro t _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by ring
  rw [Finset.sum_congr rfl step1]
  rw [Finset.sum_comm' (t' := range (j + 1)) (s' := fun u => Finset.Ico u (j + 1))
      (h := by intro x y; simp only [Finset.mem_range, Finset.mem_Ico]; omega)]
  have inner : ∀ u ∈ range (j + 1),
      (∑ t ∈ Finset.Ico u (j + 1),
        ((j.choose t : R) * (t.choose u : R)) *
          ((-a) ^ (j - t) * a ^ (t - u) * m ^ u * V u))
      = (j.choose u : R) * m ^ u * V u * (0 : R) ^ (j - u) := by
    intro u hu
    rw [Finset.mem_range] at hu
    have hu' : u ≤ j := Nat.lt_succ_iff.mp hu
    rw [Finset.sum_Ico_eq_sum_range]
    have hlen : j + 1 - u = (j - u) + 1 := by omega
    rw [hlen]
    have key : ∀ v ∈ range ((j - u) + 1),
        ((j.choose (u + v) : R) * ((u + v).choose u : R)) *
          ((-a) ^ (j - (u + v)) * a ^ ((u + v) - u) * m ^ u * V u)
        = ((j.choose u : R) * m ^ u * V u) *
            (a ^ v * (-a) ^ ((j - u) - v) * ((j - u).choose v : R)) := by
      intro v hv
      rw [Finset.mem_range] at hv
      have hv' : v ≤ j - u := Nat.lt_succ_iff.mp hv
      have hch : j.choose (u + v) * (u + v).choose u = j.choose u * (j - u).choose v := by
        have := Nat.choose_mul (n := j) (k := u + v) (s := u) (Nat.le_add_right u v)
        simpa using this
      have h1 : j - (u + v) = (j - u) - v := by omega
      have h2 : (u + v) - u = v := by omega
      rw [h1, h2]
      have hcast : ((j.choose (u + v) : R) * ((u + v).choose u : R))
          = ((j.choose u : R) * ((j - u).choose v : R)) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → R) hch
      rw [hcast]; ring
    rw [Finset.sum_congr rfl key, ← Finset.mul_sum]
    have hbin : (∑ v ∈ range ((j - u) + 1),
        a ^ v * (-a) ^ ((j - u) - v) * ((j - u).choose v : R)) = (0 : R) ^ (j - u) := by
      rw [← add_pow]; simp
    rw [hbin]
  rw [Finset.sum_congr rfl inner, Finset.sum_eq_single j]
  · simp
  · intro u hu hne
    rw [Finset.mem_range] at hu
    have : j - u ≠ 0 := by omega
    simp [zero_pow this]
  · intro h
    exact absurd (Finset.self_mem_range_succ j) h

variable {p : ℕ} [Fact p.Prime]

/-- A finitely generated `ℤ`-submodule of `Qbar` has uniformly bounded image in `ℂ_[p]`. -/
theorem fg_norm_bound (ιp : Qbar →+* ℂ_[p]) (S : Set Qbar)
    (hS : (Submodule.span ℤ S).FG) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ S, ‖ιp x‖ ≤ B := by
  obtain ⟨T, hT⟩ := hS
  refine ⟨∑ t ∈ T, ‖ιp t‖, Finset.sum_nonneg fun t _ => norm_nonneg _, ?_⟩
  have key : ∀ x ∈ Submodule.span ℤ (↑T : Set Qbar), ‖ιp x‖ ≤ ∑ t ∈ T, ‖ιp t‖ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        exact Finset.single_le_sum (f := fun t => ‖ιp t‖)
          (fun t _ => norm_nonneg _) (by simpa using hy)
    | zero => simpa using Finset.sum_nonneg fun t _ => norm_nonneg _
    | add y z _ _ hy hz =>
        refine le_trans ?_ (max_le hy hz)
        simpa using IsUltrametricDist.norm_add_le_max (ιp y) (ιp z)
    | smul c y _ hy =>
        have hc : ιp (c • y) = (c : ℂ_[p]) * ιp y := by rw [zsmul_eq_mul, map_mul, map_intCast]
        rw [hc, norm_mul]
        calc ‖(c : ℂ_[p])‖ * ‖ιp y‖ ≤ 1 * ‖ιp y‖ :=
              mul_le_mul_of_nonneg_right
                (IsUltrametricDist.norm_intCast_le_one _ c) (norm_nonneg _)
          _ = ‖ιp y‖ := one_mul _
          _ ≤ _ := hy
  intro x hx
  exact key x (hT ▸ Submodule.subset_span hx)

theorem ip_algebraicSymbol {k : ℕ} {ι : Qbar →+* ℂ} {f : UpperHalfPlane → ℂ}
    (P : Periods k ι f) (ιp : Qbar →+* ℂ_[p]) (s : Bool) (t : ℕ) (a m : ℚ) :
    ιp (algebraicSymbol P s t a m)
      = ∑ u ∈ range (t + 1), (t.choose u : ℂ_[p]) * (m : ℂ_[p]) ^ u *
          (a : ℂ_[p]) ^ (t - u) * ιp (P.value s u (-a / m)) := by
  simp only [algebraicSymbol, map_sum, map_mul, map_pow, map_natCast, map_ratCast]

end MTTCentred

open MTTCentred in
set_option linter.unusedVariables false in
theorem solution {p N k : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (α : ℂ_[p]) (hα : IsOrdinaryRoot f ιp α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Bool) (n : ℕ), 0 < n →
      ∀ (a : ℤ) (j : ℕ), j ≤ k - 2 →
        ‖∑ t ∈ Finset.range (j + 1),
          (j.choose t : ℂ_[p]) * (-(a : ℂ_[p])) ^ (j - t) *
            diskMoment f ιp P α s t n a‖ ≤
          C * ‖(p : ℂ_[p]) ^ (n * j)‖ := by
  classical
  obtain ⟨B, hB0, hB⟩ := fg_norm_bound ιp _ P.lattice_fg
  set E : ℝ := ‖ιp (f.epsilon (p : ZMod N))‖ with hE
  have hE0 : 0 ≤ E := norm_nonneg _
  refine ⟨B + E * B, by positivity, ?_⟩
  intro s n hn a j hj
  -- the two algebraic values that survive the recentring
  have hval1 : ‖ιp (P.value s j (-(a : ℚ) / (p : ℚ) ^ n))‖ ≤ B := hB _ ⟨s, j, _, hj, rfl⟩
  have hval2 : ‖ιp (P.value s j (-(a : ℚ) / (p : ℚ) ^ (n - 1)))‖ ≤ B := hB _ ⟨s, j, _, hj, rfl⟩
  -- recentring collapses each modular-symbol sum to a single algebraic value
  have key : ∀ m : ℚ,
      (∑ t ∈ range (j + 1), (j.choose t : ℂ_[p]) * (-(a : ℂ_[p])) ^ (j - t) *
        ιp (algebraicSymbol P s t (a : ℚ) m))
      = (m : ℂ_[p]) ^ j * ιp (P.value s j (-(a : ℚ) / m)) := by
    intro m
    have h2 := centered_collapse (R := ℂ_[p]) (fun u => ιp (P.value s u (-(a : ℚ) / m)))
        (m : ℂ_[p]) ((a : ℤ) : ℂ_[p]) j
    rw [← h2]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [ip_algebraicSymbol]
    simp only [Rat.cast_intCast]
  have hsum : (∑ t ∈ Finset.range (j + 1),
        (j.choose t : ℂ_[p]) * (-(a : ℂ_[p])) ^ (j - t) * diskMoment f ιp P α s t n a)
      = (α ^ n)⁻¹ * (((p : ℚ) ^ n : ℚ) : ℂ_[p]) ^ j *
            ιp (P.value s j (-(a : ℚ) / (p : ℚ) ^ n))
        - ιp (f.epsilon (p : ZMod N)) * (p : ℂ_[p]) ^ (k - 2) / α ^ (n + 1) *
            ((((p : ℚ) ^ (n - 1) : ℚ)) : ℂ_[p]) ^ j *
              ιp (P.value s j (-(a : ℚ) / (p : ℚ) ^ (n - 1))) := by
    have expand : ∀ t ∈ range (j + 1),
        (j.choose t : ℂ_[p]) * (-(a : ℂ_[p])) ^ (j - t) * diskMoment f ιp P α s t n a
        = (α ^ n)⁻¹ * ((j.choose t : ℂ_[p]) * (-(a : ℂ_[p])) ^ (j - t) *
              ιp (algebraicSymbol P s t (a : ℚ) ((p : ℚ) ^ n)))
          - ιp (f.epsilon (p : ZMod N)) * (p : ℂ_[p]) ^ (k - 2) / α ^ (n + 1) *
              ((j.choose t : ℂ_[p]) * (-(a : ℂ_[p])) ^ (j - t) *
                ιp (algebraicSymbol P s t (a : ℚ) ((p : ℚ) ^ (n - 1)))) := by
      intro t _
      simp only [diskMoment]
      ring
    rw [Finset.sum_congr rfl expand, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      key, key]
    ring
  rw [hsum]
  have hpn : ((((p : ℚ)) ^ n : ℚ) : ℂ_[p]) = (p : ℂ_[p]) ^ n := by push_cast; ring
  have hpn1 : ((((p : ℚ)) ^ (n - 1) : ℚ) : ℂ_[p]) = (p : ℂ_[p]) ^ (n - 1) := by push_cast; ring
  rw [hpn, hpn1, ← pow_mul, ← pow_mul]
  set q : ℝ := ‖(p : ℂ_[p])‖ with hq
  have hq0 : 0 ≤ q := norm_nonneg _
  have hq1 : q ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ p
  have hαn : ‖(α ^ n)⁻¹‖ = 1 := by rw [norm_inv, norm_pow, hα.1, one_pow, inv_one]
  have hαn1 : ‖α ^ (n + 1)‖ = 1 := by rw [norm_pow, hα.1, one_pow]
  have hexp : n * j ≤ (k - 2) + (n - 1) * j := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have h1 : (n' + 1) * j = n' * j + j := by ring
    omega
  have t1 : ‖(α ^ n)⁻¹ * (p : ℂ_[p]) ^ (n * j) *
      ιp (P.value s j (-(a : ℚ) / (p : ℚ) ^ n))‖ ≤ B * q ^ (n * j) := by
    rw [norm_mul, norm_mul, hαn, one_mul, norm_pow]
    calc q ^ (n * j) * ‖ιp (P.value s j (-(a : ℚ) / (p : ℚ) ^ n))‖
        ≤ q ^ (n * j) * B := by
          exact mul_le_mul_of_nonneg_left hval1 (pow_nonneg hq0 _)
      _ = B * q ^ (n * j) := by ring
  have t2 : ‖ιp (f.epsilon (p : ZMod N)) * (p : ℂ_[p]) ^ (k - 2) / α ^ (n + 1) *
      (p : ℂ_[p]) ^ ((n - 1) * j) *
      ιp (P.value s j (-(a : ℚ) / (p : ℚ) ^ (n - 1)))‖ ≤ E * B * q ^ (n * j) := by
    rw [norm_mul, norm_mul, norm_div, norm_mul, hαn1, div_one, norm_pow, norm_pow, ← hE]
    calc E * q ^ (k - 2) * q ^ ((n - 1) * j) *
            ‖ιp (P.value s j (-(a : ℚ) / (p : ℚ) ^ (n - 1)))‖
        = E * ‖ιp (P.value s j (-(a : ℚ) / (p : ℚ) ^ (n - 1)))‖ *
            q ^ ((k - 2) + (n - 1) * j) := by rw [pow_add]; ring
      _ ≤ E * B * q ^ (n * j) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hval2 hE0)
            (pow_le_pow_of_le_one hq0 hq1 hexp) (pow_nonneg hq0 _) (by positivity)
  have hrhs : ‖(p : ℂ_[p]) ^ (n * j)‖ = q ^ (n * j) := norm_pow _ _
  rw [hrhs]
  calc ‖(α ^ n)⁻¹ * (p : ℂ_[p]) ^ (n * j) * ιp (P.value s j (-(a : ℚ) / (p : ℚ) ^ n))
        - ιp (f.epsilon (p : ZMod N)) * (p : ℂ_[p]) ^ (k - 2) / α ^ (n + 1) *
            (p : ℂ_[p]) ^ ((n - 1) * j) * ιp (P.value s j (-(a : ℚ) / (p : ℚ) ^ (n - 1)))‖
      ≤ _ + _ := norm_sub_le _ _
    _ ≤ B * q ^ (n * j) + E * B * q ^ (n * j) := add_le_add t1 t2
    _ = (B + E * B) * q ^ (n * j) := by ring
end

end privateSection

public section publicSection

noncomputable section
open scoped BigOperators

open MTT in
theorem MTT.ordinary_centered_disk_bound
    {p N k : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (α : ℂ_[p]) (hα : IsOrdinaryRoot f ιp α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Bool) (n : ℕ), 0 < n →
      ∀ (a : ℤ) (j : ℕ), j ≤ k - 2 →
        ‖∑ t ∈ Finset.range (j + 1),
          (j.choose t : ℂ_[p]) * (-(a : ℂ_[p])) ^ (j - t) *
            diskMoment f ιp P α s t n a‖ ≤
          C * ‖(p : ℂ_[p]) ^ (n * j)‖ := _root_.solution hN hk ι ιp f P α hα
end

end publicSection
