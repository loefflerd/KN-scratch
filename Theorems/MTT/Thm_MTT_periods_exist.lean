/-
Based on Prove2Me node MTT.periods_exist
(5a99c269-14ef-4eaf-868f-3178fd0b9e23) by davidloeffler (2026-09-05).

Proof based on Prove2Me submission 954e0d4d-c0db-45eb-9133-4000d0b503c5
by allychan327 (2026-09-06); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import Definitions.MTT.Def_MTT_Measures

import Definitions.MTT.Def_MTT_Cohomology
import Definitions.MTT.Def_MTT_Arithmetic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Theorems.MTT.Thm_MTT_Cohomology_integral_finite_generation
import Theorems.MTT.Thm_MTT_Cohomology_base_change
import Theorems.MTT.Thm_MTT_Cohomology_integration_map
import Theorems.MTT.Thm_MTT_Cohomology_signed_evaluation
import Theorems.MTT.Thm_MTT_Cohomology_signed_packet_multiplicity_one
import Theorems.MTT.Thm_MTT_Cohomology_eigenclass_descent
import Theorems.MTT.Thm_MTT_Cohomology_evaluation_lattice

/-!
# Signed algebraic periods and a finite integral lattice

Theorem statement: `MTT.periods_exist` (`5a99c269-14ef-4eaf-868f-3178fd0b9e23`), by davidloeffler,
2026-09-05.

Proof: submission `954e0d4d-c0db-45eb-9133-4000d0b503c5`, by allychan327, 2026-09-06 (ACCEPTED);
locally adapted.

Every normalized algebraic cuspidal Hecke eigenform of positive level and weight k ≥ 2 has two
nonzero complex periods. Dividing each signed modular integral by the corresponding period gives
algebraic values; their integral span, for all rational cusps and degrees 0 through k−2, is finitely
generated. The signed projection includes one half and reflection of the polynomial.

## Explanation of the source proof

# Signed periods for a cuspidal eigenform, assembled from cohomology

## What is being built

Fix a normalized algebraic cuspidal Hecke eigenform $f$ of level $N>0$ and weight $k\ge 2$, and an
embedding $\iota:\overline{\mathbf Q}\hookrightarrow\mathbf C$. A *period system* for $f$ consists
of

* two nonzero complex numbers $\Omega^{+},\Omega^{-}$,
* algebraic numbers $v(s,j,r)\in\overline{\mathbf Q}$ for $s\in\{\pm\}$, $0\le j\le k-2$,
  $r\in\mathbf Q$, satisfying
$$\iota\bigl(v(s,j,r)\bigr)\;=\;\frac{\lambda^{s}_{j}(f,r)}{\Omega^{s}},\qquad
\lambda^{s}_{j}(f,r)=\tfrac12\Bigl(\textstyle\int_{r}^{i\infty}\!f\,X^{j}+s\,(-1)^{j}\int_{-r}^{i\infty}\!f\,X^{j}\Bigr),$$
* and the requirement that the $\mathbf Z$-span of all the $v(s,j,r)$ be a **finitely generated**
  subgroup of $\overline{\mathbf Q}$.

The point of the last clause is that $r$ ranges over *all* rational cusps: a priori one gets
infinitely many algebraic numbers, and the theorem asserts they all live in one finite lattice. This
is what later lets the $p$-adic measure be built with bounded denominators.

## The mechanism

The proof is pure assembly. Nothing analytic happens here; every analytic input has been pushed into
the imported nodes.

**Step 1 — the two signed classes.** The integration map $I$ (`integration_map`) sends cusp forms to
compactly supported cohomology $H^1_c(\Gamma_1(N),\operatorname{Sym}^{k-2}\mathbf C^2)$ so that the
$X^jY^{k-2-j}$-coefficient of $I(f)([\infty]-[r])$ is $\binom{k-2}{j}\int_r^{i\infty}f\,X^j$.
Applying `signed_evaluation` to $I$ produces, for each sign $s$, a class $\Phi^{s}$ which
* evaluates to $\binom{k-2}{j}\lambda^{s}_{j}(f,r)$, and
* lies in the eigenpacket: it satisfies the prime-Hecke equations $T_\ell\Phi^s=\iota(a_\ell)\Phi^s$
  for every prime $\ell$, the $\Gamma_0(N)$ nebentype law with character $\iota\circ\varepsilon$,
  and the reflection equation $\mathcal R\Phi^s=s\,\Phi^s$.

**Step 2 — descent.** The eigenpacket is at most one-dimensional (`signed_packet_multiplicity_one`),
the integral cohomology is a finitely generated $\mathbf Z$-module (`integral_finite_generation`),
and flat base change holds for $\overline{\mathbf Q}$ and $\mathbf C$ (`base_change`, applied
through the instances $\mathbf Z\to\mathbf Q\to K$ for a field $K$ of characteristic $0$). Under
exactly these hypotheses `eigenclass_descent` produces
$$\Omega^{s}\in\mathbf C^{\times},\qquad \Psi^{s}\in
H^1_c(\Gamma_1(N),\operatorname{Sym}^{k-2}\overline{\mathbf Q}^2),\qquad
\Psi^{s}\ \text{extends coefficientwise to}\ (\Omega^{s})^{-1}\Phi^{s}.$$
The period is *defined* as this scalar. That is the whole content of "the period exists": it is the
ratio between the analytically defined class and an algebraically defined one on the same line.

**Step 3 — the values.** Set
$$v(s,j,r)\;=\;\frac{\operatorname{ev}_{j,r}(\Psi^{s})}{\binom{k-2}{j}}\in\overline{\mathbf Q}.$$
Coefficientwise extension commutes with the evaluation functionals — this is the lemma
`evaluation_extends`, which is just $\operatorname{coeff}_d(\text{map
}\iota\,P)=\iota(\operatorname{coeff}_d P)$ — so
$$\iota\bigl(\operatorname{ev}_{j,r}\Psi^{s}\bigr)=\operatorname{ev}_{j,r}\bigl((\Omega^{s})^{-1}\Phi^{s}\bigr)=(\Omega^{s})^{-1}\binom{k-2}{j}\lambda^{s}_{j}(f,r),$$
and dividing by $\binom{k-2}{j}$, which is a nonzero integer for $j\le k-2$, gives exactly the
comparison identity. Note that the denominators cancel *before* any lattice claim is made; this is
why the binomial factor is carried through the definition of `IntegralClass` rather than absorbed
into the period.

**Step 4 — the lattice.** The set whose $\mathbf Z$-span must be finitely generated is, term for
term, the set appearing in `evaluation_lattice` for the pair $(\Psi^{+},\Psi^{-})$. So the last
clause is discharged by that node verbatim.

## Where the difficulty is not

It is worth being explicit that this node proves no transcendence, no rationality of $L$-values, and
no bound on denominators by itself. It records that the standard chain

$$\text{Eichler–Shimura}\ \longrightarrow\ \text{multiplicity one}\ \longrightarrow\ \text{descent}\
\longrightarrow\ \text{integral lattice}$$

closes up, with the two periods produced as the descent scalars for the two signs. The genuinely new
mathematics sits in the imported nodes: the construction and injectivity of $I$, the signed
eigenclass construction, multiplicity one, and flat base change.

## A small technical remark

Flatness of $\mathbf C$ and of $\overline{\mathbf Q}$ over $\mathbf Z$ is not in the ambient library
as an instance. It is supplied here in two steps: $\mathbf Q$ is flat over $\mathbf Z$ because it is
the localization of $\mathbf Z$ at its nonzero divisors, and any field $K$ containing $\mathbf Q$ is
free, hence flat, over $\mathbf Q$; transitivity of flatness gives $\mathbf Z\to K$. This is the
only place where the characteristic-zero hypothesis is used.

<!-- Generated by add_prove2me_provenance.py -->
-/

section privateSection

set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

namespace P2MPE

/-- `ℚ` is a flat `ℤ`-module: it is the localization of `ℤ` at its nonzero divisors. -/
instance flat_int_rat : Module.Flat ℤ ℚ :=
  IsLocalization.flat ℚ (nonZeroDivisors ℤ)

/-- Any field that is a `ℚ`-algebra is flat over `ℤ`. -/
instance flat_int_of_rat_algebra (K : Type*) [Field K] [Algebra ℚ K] :
    Module.Flat ℤ K :=
  haveI : Module.Free ℚ K := Module.Free.of_divisionRing ℚ K
  haveI : Module.Flat ℚ K := Module.Flat.of_free
  Module.Flat.trans ℤ ℚ K

/-- Coefficientwise extension of classes transports the integral evaluation
functionals along the coefficient homomorphism. -/
theorem evaluation_extends {N n : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (ι : R →+* S) (ψ : Hc N n R) (φ : Hc N n S) (h : Extends ι ψ φ) (j : ℕ) (r : ℚ) :
    evaluation j r φ = ι (evaluation j r ψ) := by
  show AddMonoidAlgebra.coeff (φ.val (OnePoint.infty, (r : Cusp))) _
      = ι (AddMonoidAlgebra.coeff (ψ.val (OnePoint.infty, (r : Cusp))) _)
  rw [h OnePoint.infty ((r : ℚ) : Cusp)]
  exact MvPolynomial.coeff_map _ _ _

end P2MPE

open P2MPE in
theorem solution {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) :
    Nonempty (MTT.Periods k ι f.form) := by
  have hZ : Module.Finite ℤ (Hc N (k - 2) ℤ) :=
    MTT.Cohomology.integral_finite_generation hN
  have hQ : BaseChange N (k - 2) MTT.Qbar := MTT.Cohomology.base_change hN _
  have hC : BaseChange N (k - 2) ℂ := MTT.Cohomology.base_change hN _
  obtain ⟨I, -, hT, hI⟩ := MTT.Cohomology.integration_map (N := N) (k := k) hN hk
  obtain ⟨φ, hφ⟩ := MTT.Cohomology.signed_evaluation hN hk I hI hT ι f
  have hdesc : ∀ s : Bool, ∃ ω : ℂ, ω ≠ 0 ∧
      ∃ ψ : Hc N (k - 2) MTT.Qbar, Extends ι ψ (ω⁻¹ • φ s) := fun s =>
    MTT.Cohomology.eigenclass_descent hZ hQ hC ι f.epsilon f.coeff s
      (fun a b ha hb => MTT.Cohomology.signed_packet_multiplicity_one hN hk ι f s a b ha hb)
      (φ s) (hφ s).2
  choose ω hω ψ hψ using hdesc
  refine ⟨{ omega := ω, omega_ne := hω,
            value := fun s j r => evaluation j r (ψ s) / ((k - 2).choose j : MTT.Qbar),
            comparison := ?_, lattice_fg := ?_ }⟩
  · intro s j r hj
    have hbin : ((k - 2).choose j : ℂ) ≠ 0 := by
      exact_mod_cast Nat.cast_ne_zero.mpr (Nat.choose_pos hj).ne'
    have hkey : ι (evaluation j r (ψ s)) = (ω s)⁻¹ * evaluation j r (φ s) := by
      rw [← evaluation_extends ι (ψ s) _ (hψ s) j r]
      exact map_smul (evaluation j r) _ (φ s)
    rw [map_div₀, map_natCast, hkey, (hφ s).1 j r hj]
    field_simp
  · exact MTT.Cohomology.evaluation_lattice hZ hQ ψ
end

end privateSection

public section publicSection

noncomputable section
open scoped BigOperators

theorem MTT.periods_exist
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) :
    Nonempty (MTT.Periods k ι f.form) := _root_.solution hN hk ι f
end

end publicSection
