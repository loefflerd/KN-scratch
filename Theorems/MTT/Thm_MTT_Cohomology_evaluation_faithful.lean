/-
Based on Prove2Me node MTT.Cohomology.evaluation_faithful
(d8288d98-3f41-45b3-86c4-c5bc698df897) by allychan327 (2026-09-06).

Proof based on Prove2Me submission e37d0f7f-a999-455a-b326-71e7d5304cac
by allychan327 (2026-09-06); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import Definitions.MTT.Def_MTT_Cohomology

/-!
# Integral evaluations on paths to infinity separate classes

Theorem statement: `MTT.Cohomology.evaluation_faithful` (`d8288d98-3f41-45b3-86c4-c5bc698df897`), by
allychan327, 2026-09-06.

Proof: submission `e37d0f7f-a999-455a-b326-71e7d5304cac`, by allychan327, 2026-09-06 (ACCEPTED);
locally adapted.

Two compactly supported cohomology classes with the same integral coefficient evaluations on every
path from the cusp at infinity to a rational cusp, in every degree from 0 to n, are equal. The
coefficient module is homogeneous of degree n in two variables, so the listed evaluations exhaust
the coefficients of the value at each such path; the cocycle relation then propagates the agreement
to all pairs of cusps. This holds over an arbitrary commutative coefficient ring.

## Explanation of the source proof

# Modular symbols are determined by their values on paths to the cusp $\infty$

## Statement

Let $\Gamma_1(N)$ act on $\operatorname{Sym}^n(R^2)$, realised as the homogeneous binary forms of
degree $n$ over a commutative ring $R$, and let
$$H^1_c\bigl(\Gamma_1(N),\operatorname{Sym}^n R^2\bigr)$$
be the modular-symbol model: functions $\varphi$ on ordered pairs of cusps with values in
$\operatorname{Sym}^n$, satisfying the cocycle relation $\varphi(x,y)+\varphi(y,z)=\varphi(x,z)$ and
$\Gamma_1(N)$-equivariance. For $0\le j\le n$ and $r\in\mathbf Q$ write
$$\operatorname{ev}_{j,r}(\varphi)\;=\;\text{the coefficient of }X^{j}Y^{\,n-j}\text{ in
}\varphi\bigl([\infty],[r]\bigr).$$
The claim is that this countable family of $R$-linear functionals is **jointly faithful**: if
$\operatorname{ev}_{j,r}(\varphi)=\operatorname{ev}_{j,r}(\psi)$ for all $j\le n$ and all
$r\in\mathbf Q$, then $\varphi=\psi$.

## Why it is true

By linearity it suffices to prove that $\varphi=0$ whenever all $\operatorname{ev}_{j,r}(\varphi)$
vanish. There are three steps, and each is essentially forced.

**1. The listed coefficients are all the coefficients.** The value $\varphi([\infty],[r])$ lies in
$\operatorname{Sym}^n$, i.e. it is a homogeneous binary form of degree $n$. A monomial
$X^{d_0}Y^{d_1}$ occurring in it must satisfy $d_0+d_1=n$, hence $d_1=n-d_0$ and $d_0\le n$: the
exponent vector is exactly the one used in $\operatorname{ev}_{d_0,r}$. Any monomial of the wrong
total degree has coefficient $0$ by homogeneity. So the hypothesis says every coefficient of
$\varphi([\infty],[r])$ vanishes, i.e.
$$\varphi([\infty],[r])=0\qquad\text{for every }r\in\mathbf Q .$$
In Lean this is the lemma `val_infty_eq_zero`: after `MvPolynomial.ext` one splits on whether the
exponent vector has degree $n$; in the affirmative case `eq_mono` identifies it with the monomial of
`evaluation`, and in the negative case `IsHomogeneous.coeff_eq_zero` closes the goal. The
identification `eq_mono` is where the two-variable hypothesis is used — it is what makes the single
index $j$ enough.

**2. The diagonal vanishes.** Taking $x=y=z$ in the cocycle relation gives
$\varphi(x,x)+\varphi(x,x)=\varphi(x,x)$, hence $\varphi(x,x)=0$. In particular
$\varphi([\infty],[\infty])=0$, which is the remaining value at the cusp $\infty$ not covered by
step 1. This is the only place the argument uses that the coefficient module is a group rather than
a monoid.

**3. Every path decomposes through $\infty$.** The cocycle relation with $x=[\infty]$ gives
$$\varphi(x,y)=\varphi([\infty],y)-\varphi([\infty],x),$$
so $\varphi$ is determined by its values on paths issuing from $\infty$. Since $\mathbf P^1(\mathbf
Q)=\mathbf Q\cup\{\infty\}$, steps 1 and 2 cover all such values, and both terms vanish. Hence
$\varphi=0$ as a function on pairs of cusps, and therefore as an element of the submodule.

## Remarks on scope

The proof uses neither $N>0$ nor any property of $R$ beyond being a commutative ring, and in
particular it does not use $\Gamma_1(N)$-equivariance at all. Equivariance is what makes the space
small; faithfulness of the evaluations is a statement about the cocycle condition alone. It is also
worth noting what is *not* claimed: nothing here says which families of values
$(\operatorname{ev}_{j,r})_{j,r}$ actually arise. Surjectivity onto the space of Manin relations is
a genuinely harder statement, and is exactly what Manin's presentation theorem supplies.

## Consequences used elsewhere

Two follow-ups are immediate. First, the Eichler–Shimura class of a cusp form is unique: two classes
whose evaluations both reproduce $\binom{n}{j}\int_{r}^{i\infty}f\,X^{j}$ must coincide, so no
normalisation choice is hidden in the phrase "the integration class". Second, injectivity of the
integration map reduces to the purely analytic assertion that a cusp form with vanishing period
integrals is zero, since a class in the kernel has all evaluations zero, and $\binom{n}{j}$ is
invertible in $\mathbf C$.

<!-- Generated by add_prove2me_provenance.py -->
-/

section privateSection

set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators
open MTT.Cohomology

namespace P2MEF

open MvPolynomial

variable {N n : ℕ} {R : Type*} [CommRing R]

/-- The exponent vector of `X^j Y^(n-j)`, exactly as it occurs in `evaluation`. -/
def mono (n j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i : Fin 2 => if i = 0 then j else n - j)

theorem mono_apply (n j : ℕ) (i : Fin 2) : mono n j i = if i = 0 then j else n - j := rfl

theorem evaluation_apply (j : ℕ) (r : ℚ) (φ : Hc N n R) :
    evaluation j r φ = AddMonoidAlgebra.coeff (φ.val (OnePoint.infty, (r : Cusp))) (mono n j) :=
  rfl

theorem deg_eq (d : Fin 2 →₀ ℕ) : d.degree = d 0 + d 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]

/-- A degree-`n` exponent vector in two variables is `X^j Y^(n-j)` for `j = d 0`. -/
theorem eq_mono (d : Fin 2 →₀ ℕ) (j : ℕ) (hj : d 0 = j) (hd : d.degree = n) :
    d = mono n j := by
  rw [deg_eq] at hd
  ext i
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · rw [mono_apply]; simp [hj]
  · rw [mono_apply]; simp; omega

/-- A class all of whose integral evaluations on `[∞] − [r]` vanish is zero on those paths. -/
theorem val_infty_eq_zero (φ : Hc N n R)
    (h : ∀ j r, j ≤ n → evaluation j r φ = 0) (r : ℚ) :
    φ.val (OnePoint.infty, (r : Cusp)) = 0 := by
  have hhom : (φ.val (OnePoint.infty, (r : Cusp))).IsHomogeneous n :=
    (MvPolynomial.mem_homogeneousSubmodule _ _).mp (φ.2.1 _ _)
  refine MvPolynomial.ext _ _ fun d => ?_
  change AddMonoidAlgebra.coeff (φ.val (OnePoint.infty, (r : Cusp))) d = 0
  by_cases hd : d.degree = n
  · have hle : d 0 ≤ n := by rw [deg_eq] at hd; omega
    rw [eq_mono d (d 0) rfl hd]
    exact h (d 0) r hle
  · exact hhom.coeff_eq_zero hd

theorem diag_zero (φ : Hc N n R) (x : Cusp) : φ.val (x, x) = 0 := by
  have h := φ.2.2.1 x x x
  have h2 : φ.val (x, x) + φ.val (x, x) - φ.val (x, x) = 0 := by rw [h]; simp
  simpa using h2

theorem val_eq (φ : Hc N n R) (x y : Cusp) :
    φ.val (x, y) = φ.val (OnePoint.infty, y) - φ.val (OnePoint.infty, x) := by
  have h := φ.2.2.1 OnePoint.infty x y
  rw [← h]; ring

/-- Integral coefficient evaluation on the paths `[∞] − [r]` is faithful. -/
theorem hc_eq_zero_of_evaluations (φ : Hc N n R)
    (h : ∀ j r, j ≤ n → evaluation j r φ = 0) : φ = 0 := by
  have hall : ∀ y : Cusp, φ.val (OnePoint.infty, y) = 0 := by
    intro y
    induction y using OnePoint.rec with
    | infty => exact diag_zero φ _
    | coe r => exact val_infty_eq_zero φ h r
  refine Subtype.ext (funext fun D => ?_)
  obtain ⟨x, y⟩ := D
  show φ.val (x, y) = 0
  rw [val_eq φ x y, hall, hall, sub_zero]

end P2MEF

open P2MEF in
theorem solution {N n : ℕ} {R : Type*} [CommRing R] (φ ψ : Hc N n R)
    (h : ∀ j r, j ≤ n → evaluation j r φ = evaluation j r ψ) : φ = ψ := by
  have := hc_eq_zero_of_evaluations (φ - ψ) (fun j r hj => by
    rw [map_sub, h j r hj, sub_self])
  exact sub_eq_zero.mp this
end

end privateSection

public section publicSection

noncomputable section
open scoped BigOperators
open MTT.Cohomology

theorem MTT.Cohomology.evaluation_faithful
    {N n : ℕ} {R : Type*} [CommRing R] (φ ψ : Hc N n R)
    (h : ∀ j r, j ≤ n → evaluation j r φ = evaluation j r ψ) :
    φ = ψ := _root_.solution φ ψ h
end

end publicSection
