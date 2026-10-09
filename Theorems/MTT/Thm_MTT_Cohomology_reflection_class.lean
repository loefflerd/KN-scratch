/-
Based on Prove2Me node MTT.Cohomology.reflection_class
(c85142f2-67d2-4548-b57b-a469f28c8e7b) by allychan327 (2026-09-06).

Proof based on Prove2Me submission b65c560e-ff07-4802-bc88-856b821148e6
by allychan327 (2026-09-06); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import Definitions.MTT.Def_MTT_Cohomology
public import Mathlib.RingTheory.Flat.Basic

/-!
# The reflection is a Hecke-equivariant involution on modular symbols

Theorem statement: `MTT.Cohomology.reflection_class` (`c85142f2-67d2-4548-b57b-a469f28c8e7b`), by
allychan327, 2026-09-06.

Proof: submission `b65c560e-ff07-4802-bc88-856b821148e6`, by allychan327, 2026-09-06 (ACCEPTED);
locally adapted.

Write $J=\begin{pmatrix}-1&0\\0&1\end{pmatrix}$ and let
$$(\mathcal R\varphi)(x,y) = J\cdot\varphi(Jx,\,Jy)$$
be the reflection operator on cocycles of weight $n$ with coefficients in a commutative ring $R$; on
cusps $J$ acts by $r\mapsto -r$ and fixes $\infty$, and on binary forms by $X\mapsto -X$, $Y\mapsto
Y$.
This is the involution whose $\pm 1$-eigenspaces cut out the signed modular symbols. The theorem
asserts three things about $\mathcal R$ on
$H^1_c(\Gamma_1(N),\operatorname{Sym}^n R^2)$.

**(i) $\mathcal R$ preserves the space.** If $\varphi$ is a $\Gamma_1(N)$-equivariant cocycle with
values in $\operatorname{Sym}^n$, so is $\mathcal R\varphi$. Equivariance uses that
$J\Gamma_1(N)J^{-1}=\Gamma_1(N)$, since conjugation by $J$ sends
$\begin{pmatrix}a&b\\c&d\end{pmatrix}$ to $\begin{pmatrix}a&-b\\-c&d\end{pmatrix}$.

**(ii) $\mathcal R$ commutes with the prime Hecke operators.** For every $\ell$ and every scalar
$e\in R$,
$$\mathcal R\bigl(T_\ell^{(e)}\varphi\bigr)=T_\ell^{(e)}\bigl(\mathcal R\varphi\bigr),
\qquad T_\ell^{(e)}=\sum_{b=0}^{\ell-1}\Bigl|\begin{pmatrix}1&b\\0&\ell\end{pmatrix}
+ e\Bigl|\begin{pmatrix}\ell&0\\0&1\end{pmatrix}.$$
The identity comes from
$J\begin{pmatrix}1&b\\0&\ell\end{pmatrix}J=\begin{pmatrix}1&-b\\0&\ell\end{pmatrix}$
together with
$\begin{pmatrix}1&-b\\0&\ell\end{pmatrix}=\begin{pmatrix}1&-1\\0&1\end{pmatrix}\begin{pmatrix}1&\ell-b\\0&\ell\end{pmatrix}$:
the coset representatives are permuted by $b\mapsto \ell-b \pmod \ell$, and the leftover unipotent
matrix lies in $\Gamma_1(N)$, so it acts trivially on $\varphi$. The second term is fixed because
$J$ commutes with $\operatorname{diag}(\ell,1)$.

**(iii) $\mathcal R$ preserves the nebentype law.** If $\varphi$ satisfies
$\varphi(\gamma x,\gamma y)=e(d)\,\gamma\cdot\varphi(x,y)$ for all $\gamma\in\Gamma_0(N)$, then so
does $\mathcal R\varphi$, with the same character $e$; conjugation by $J$ preserves $\Gamma_0(N)$
and
leaves the lower-right entry $d$ unchanged.

Together these say that $\mathcal R$ is an involution of the Hecke module of modular symbols, so the
signed projections $\tfrac12(1\pm\mathcal R)$ are Hecke-equivariant idempotents. This is the
algebraic
input behind every "plus/minus modular symbol" construction.

## Explanation of the source proof

## The reflection is a Hecke-equivariant involution

Throughout, $J=\begin{pmatrix}-1&0\\0&1\end{pmatrix}$, classes are $\Gamma_1(N)$-equivariant
cocycles
$\varphi$ on pairs of cusps with values in binary forms of degree $n$ over a commutative ring $R$,
and
$$(\mathcal R\varphi)(x,y)=J\cdot\varphi(Jx,Jy),\qquad
(\varphi|_A)(x,y)=\operatorname{adj}(A)\cdot\varphi(Ax,Ay).$$
Matrices act on cusps by Möbius transformations and on forms by
$(\operatorname{act}A\,P)(X,Y)=P((X,Y)A)$.

### 0. Two composition rules for the cusp action

`fractional` is defined by explicit formulas with case splits on vanishing denominators, so
composition is not free. Two special cases suffice for everything below, and both avoid any
determinant hypothesis:

* **Left factor with bottom row $(0,1)$.** For $U=\begin{pmatrix}a&b\\0&1\end{pmatrix}$ and any
  integral $g$, $\ U\cdot(g\cdot x)=(Ug)\cdot x$. The point is that $U$ never sends a finite cusp to
  $\infty$, so the case split on the outer denominator is trivial and the inner one matches on the
  nose; the finite case is a one-line clearing of denominators. Both $J$ and the unipotent matrices
  $\begin{pmatrix}1&t\\0&1\end{pmatrix}$ are of this shape.
* **Right factor $J$.** For any integral $g$, $\ g\cdot(J\cdot x)=(gJ)\cdot x$. Here $gJ$ negates
  the
  first column of $g$, so the two case splits are literally the same condition, and the two values
  agree after cancelling a sign.

Restricted to $SL_2(\mathbf Z)$, `fractional` agrees with the projective-line action used to define
`cuspAct`; this is checked directly against the two `OnePoint` formulas.

Finally, $\operatorname{act}$ is a monoid homomorphism, $\operatorname{act}(AB)=\operatorname{act}A
\circ\operatorname{act}B$, which follows from composing the substitutions $X_i\mapsto\sum_a
A_{ai}X_a$.

### 1. $\mathcal R$ preserves the space of classes

Homogeneity is preserved because $\operatorname{act}A$ substitutes linear forms, so it multiplies
degrees by $1$. The cocycle relation is preserved because $\operatorname{act}J$ is additive.

For equivariance, set $\gamma'=J\gamma J$. Then $\gamma'\in SL_2(\mathbf Z)$ (two factors of
$\det J=-1$), and its entries are $\begin{pmatrix}a&-b\\-c&d\end{pmatrix}$, so
$\gamma'\in\Gamma_1(N)$
whenever $\gamma$ is. The two composition rules give
$$J\cdot(\gamma\cdot x)=(J\gamma)\cdot x=(\gamma'J)\cdot x=\gamma'\cdot(J\cdot x),$$
using $J^2=1$. Applying the equivariance of $\varphi$ for $\gamma'$ and then
$J\cdot\operatorname{adj}$-free bookkeeping,
$$\operatorname{act}J\circ\operatorname{act}\gamma'=\operatorname{act}(J\gamma')
=\operatorname{act}(\gamma J)=\operatorname{act}\gamma\circ\operatorname{act}J,$$
which is exactly equivariance of $\mathcal R\varphi$.

### 2. $\mathcal R$ commutes with the prime Hecke operators

The general step is a single lemma. Suppose $A,A'$ are integral matrices and $t\in\mathbf Z$ satisfy
$$A J = \begin{pmatrix}1&t\\0&1\end{pmatrix}(JA'),\qquad
J\,\operatorname{adj}(A)\begin{pmatrix}1&t\\0&1\end{pmatrix}=\operatorname{adj}(A')\,J .$$
Then $\mathcal R(\varphi|_A)=(\mathcal R\varphi)|_{A'}$. Indeed the first identity moves the cusp
arguments across, at the cost of a unipotent matrix which lies in $\Gamma_1(N)$ for every $t$ and is
therefore absorbed by the equivariance of $\varphi$; the second identity then matches the two
coefficient actions.

For
$T_\ell^{(e)}=\sum_{b=0}^{\ell-1}\big|_{\left(\begin{smallmatrix}1&b\\0&\ell\end{smallmatrix}\right)}
+\,e\big|_{\left(\begin{smallmatrix}\ell&0\\0&1\end{smallmatrix}\right)}$ the hypotheses hold with

* $A=A'=\begin{pmatrix}1&0\\0&\ell\end{pmatrix}$, $t=0$;
* $A=\begin{pmatrix}1&b\\0&\ell\end{pmatrix}$, $A'=\begin{pmatrix}1&\ell-b\\0&\ell\end{pmatrix}$,
  $t=1$, for $1\le b\le \ell-1$;
* $A=A'=\begin{pmatrix}\ell&0\\0&1\end{pmatrix}$, $t=0$.

So $\mathcal R$ permutes the coset terms by the involution $b\mapsto \ell-b \pmod \ell$ of
$\{0,\dots,\ell-1\}$, and summing over that involution — as an explicit permutation of `Fin l`, so
the degenerate values $\ell=0,1$ need no special treatment — gives
$\mathcal R(T_\ell^{(e)}\varphi)=T_\ell^{(e)}(\mathcal R\varphi)$.

### 3. $\mathcal R$ preserves the nebentype law

Same conjugation as in §1, now with $\gamma\in\Gamma_0(N)$: $\gamma'=J\gamma J$ again lies in
$\Gamma_0(N)$ since its lower-left entry is $-c$, and — this is the point — its lower-right entry is
the *same* $d$. So the character value $e(d)$ is unchanged, and it commutes past
$\operatorname{act}J$ because the coefficient action is $R$-linear. $\square$

Together the three statements say that $\mathcal R$ is an involution of the Hecke module of modular
symbols over any coefficient ring, so $\tfrac12(1\pm\mathcal R)$ are Hecke-equivariant idempotents
whenever $2$ is invertible — the algebraic input behind every plus/minus modular symbol.

<!-- Generated by add_prove2me_provenance.py -->
-/

section privateSection

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open scoped BigOperators
open MTT.Cohomology


namespace P2MSE

open MvPolynomial

variable {R : Type*} [CommRing R]

/-! ### The coefficient action is a monoid homomorphism -/

theorem act_apply (A : Matrix (Fin 2) (Fin 2) ℤ) (P : Binary R) :
    act A P = MvPolynomial.bind₁ (fun i : Fin 2 =>
      ∑ a : Fin 2, (A a i : R) • MvPolynomial.X a) P := rfl

theorem act_one (P : Binary R) : act 1 P = P := by
  rw [act_apply]
  have h : (fun i : Fin 2 => ∑ a : Fin 2, ((1 : Matrix (Fin 2) (Fin 2) ℤ) a i : R) •
      MvPolynomial.X a) = fun i : Fin 2 => (MvPolynomial.X i : Binary R) := by
    funext i
    rw [Fin.sum_univ_two]
    fin_cases i <;> simp [Matrix.one_apply]
  rw [h, MvPolynomial.bind₁_X_left, AlgHom.id_apply]

theorem act_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) (P : Binary R) :
    act (A * B) P = act A (act B P) := by
  simp only [act_apply]
  rw [MvPolynomial.bind₁_bind₁]
  have hfun : (fun i : Fin 2 => (MvPolynomial.bind₁
        (fun j : Fin 2 => (∑ a : Fin 2, (A a j : R) • MvPolynomial.X a : Binary R)))
        (∑ a : Fin 2, (B a i : R) • MvPolynomial.X a : Binary R))
      = fun i : Fin 2 => (∑ a : Fin 2, ((A * B) a i : R) • MvPolynomial.X a : Binary R) := by
    funext i
    rw [map_sum]
    simp only [map_smul, MvPolynomial.bind₁_X_right, Fin.sum_univ_two, Matrix.mul_apply]
    match_scalars <;> ring
  rw [hfun]

theorem act_add (A : Matrix (Fin 2) (Fin 2) ℤ) (P Q : Binary R) :
    act A (P + Q) = act A P + act A Q := map_add _ _ _

theorem reflection_add (φ ψ : (Cusp × Cusp) → Binary R) :
    reflection (φ + ψ) = reflection φ + reflection ψ := by
  funext D; simp [reflection, act_add]

theorem reflection_smul (c : R) (φ : (Cusp × Cusp) → Binary R) :
    reflection (c • φ) = c • reflection φ := by
  funext D; simp [reflection]

end P2MSE

namespace P2MRC

open MvPolynomial

/-! ### The fractional-linear action in coordinates -/

theorem frac_infty (g : Matrix (Fin 2) (Fin 2) ℤ) :
    fractional g OnePoint.infty
      = if g 1 0 = 0 then OnePoint.infty else ((((g 0 0 : ℤ) : ℚ) / ((g 1 0 : ℤ) : ℚ)) : Cusp) :=
  rfl

theorem frac_coe (g : Matrix (Fin 2) (Fin 2) ℤ) (r : ℚ) :
    fractional g ((r : ℚ) : Cusp)
      = if ((g 1 0 : ℤ) : ℚ) * r + ((g 1 1 : ℤ) : ℚ) = 0 then OnePoint.infty
        else (((((g 0 0 : ℤ) : ℚ) * r + ((g 0 1 : ℤ) : ℚ)) /
          (((g 1 0 : ℤ) : ℚ) * r + ((g 1 1 : ℤ) : ℚ))) : Cusp) :=
  rfl

/-- Left multiplication by a matrix with bottom row `(0,1)` composes with the action. -/
theorem frac_upper_comp (a b : ℤ) (g : Matrix (Fin 2) (Fin 2) ℤ) (x : Cusp) :
    fractional !![a, b; 0, 1] (fractional g x) = fractional (!![a, b; 0, 1] * g) x := by
  have u00 : (!![a, b; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = a := by simp
  have u01 : (!![a, b; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = b := by simp
  have u10 : (!![a, b; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by simp
  have u11 : (!![a, b; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 := by simp
  have e00 : (!![a, b; 0, 1] * g) 0 0 = a * g 0 0 + b * g 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (!![a, b; 0, 1] * g) 0 1 = a * g 0 1 + b * g 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (!![a, b; 0, 1] * g) 1 0 = g 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (!![a, b; 0, 1] * g) 1 1 = g 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  induction x using OnePoint.rec with
  | infty =>
      rw [frac_infty g, frac_infty (!![a, b; 0, 1] * g), e00, e10]
      by_cases h : g 1 0 = 0
      · rw [ite_eq_left h, ite_eq_left h, frac_infty, u10, ite_eq_left rfl]
      · rw [ite_eq_right h, ite_eq_right h, frac_coe, u10, u11, u00, u01, ite_eq_right (by norm_num)]
        have hq : ((g 1 0 : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr h
        congr 1
        push_cast
        rw [zero_mul, zero_add, div_one]
        field_simp
  | coe r =>
      rw [frac_coe g r, frac_coe (!![a, b; 0, 1] * g) r, e00, e01, e10, e11]
      by_cases h : ((g 1 0 : ℤ) : ℚ) * r + ((g 1 1 : ℤ) : ℚ) = 0
      · rw [ite_eq_left h, ite_eq_left h, frac_infty, u10, ite_eq_left rfl]
      · have hD : ((g 1 0 : ℤ) : ℚ) * r + ((g 1 1 : ℤ) : ℚ) ≠ 0 := h
        rw [ite_eq_right h, ite_eq_right h, frac_coe, u10, u11, u00, u01, ite_eq_right (by norm_num)]
        congr 1
        push_cast
        rw [zero_mul, zero_add, div_one, eq_div_iff hD, add_mul, mul_assoc,
          div_mul_cancel₀ _ hD]
        ring

/-- The reflection matrix. -/
abbrev Jm : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 0; 0, 1]

/-- Right multiplication by the reflection matrix composes with the action. -/
theorem frac_comp_J (g : Matrix (Fin 2) (Fin 2) ℤ) (x : Cusp) :
    fractional g (fractional Jm x) = fractional (g * Jm) x := by
  have e00 : (g * Jm) 0 0 = -g 0 0 := by simp [Jm, Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (g * Jm) 0 1 = g 0 1 := by simp [Jm, Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (g * Jm) 1 0 = -g 1 0 := by simp [Jm, Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (g * Jm) 1 1 = g 1 1 := by simp [Jm, Matrix.mul_apply, Fin.sum_univ_two]
  induction x using OnePoint.rec with
  | infty =>
      rw [frac_infty Jm]
      norm_num [Jm]
      rw [frac_infty g, frac_infty (g * Jm), e00, e10]
      by_cases h : g 1 0 = 0
      · rw [ite_eq_left h, ite_eq_left (by simp [h])]
      · rw [ite_eq_right h, ite_eq_right (by simpa using h)]
        push_cast
        rw [neg_div_neg_eq]
  | coe r =>
      rw [frac_coe Jm r]
      norm_num [Jm]
      rw [frac_coe g (-r), frac_coe (g * Jm) r, e00, e01, e10, e11]
      by_cases h : ((g 1 0 : ℤ) : ℚ) * (-r) + ((g 1 1 : ℤ) : ℚ) = 0
      · rw [ite_eq_left h, ite_eq_left (by push_cast; linear_combination h)]
      · rw [ite_eq_right h, ite_eq_right (by push_cast; intro hc; exact h (by
          linear_combination hc))]
        congr 1
        push_cast
        ring

end P2MRC

namespace P2MRC

open MvPolynomial P2MSE

abbrev SL2 := Matrix.SpecialLinearGroup (Fin 2) ℤ

/-! ### `fractional` restricted to `SL(2,ℤ)` is the cusp action -/

theorem cuspAct_infty (g : SL2) :
    cuspAct g OnePoint.infty
      = if (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 then OnePoint.infty
        else ((((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℚ)
              / ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℚ)) : ℚ) := by
  rw [cuspAct, OnePoint.smul_infty_eq_ite]
  simp [Matrix.SpecialLinearGroup.mapGL]

theorem cuspAct_coe (g : SL2) (r : ℚ) :
    cuspAct g ((r : ℚ) : Cusp)
      = if (((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ℚ) * r
            + (((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℚ) = 0 then OnePoint.infty
        else (((((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ℚ) * r
            + (((g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ℚ)) /
          ((((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ℚ) * r
            + (((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℚ)) : ℚ) := by
  rw [cuspAct, OnePoint.smul_some_eq_ite]
  simp [Matrix.SpecialLinearGroup.mapGL]

theorem frac_eq_cuspAct (g : SL2) (x : Cusp) :
    fractional (g : Matrix (Fin 2) (Fin 2) ℤ) x = cuspAct g x := by
  induction x using OnePoint.rec with
  | infty => rw [frac_infty, cuspAct_infty]
  | coe r => rw [frac_coe, cuspAct_coe]

/-! ### Conjugation by the reflection -/

theorem Jm_mul_Jm : Jm * Jm = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Jm, Matrix.mul_apply]

theorem det_Jm : Jm.det = -1 := by simp [Jm, Matrix.det_fin_two_of]

/-- `J γ J`, an element of `SL(2,ℤ)` again. -/
def conjJ (g : SL2) : SL2 :=
  ⟨Jm * (g : Matrix (Fin 2) (Fin 2) ℤ) * Jm, by
    rw [Matrix.det_mul, Matrix.det_mul, g.2, det_Jm]; ring⟩

theorem conjJ_val (g : SL2) :
    (conjJ g : Matrix (Fin 2) (Fin 2) ℤ) = Jm * (g : Matrix (Fin 2) (Fin 2) ℤ) * Jm := rfl

theorem frac_J_cuspAct (g : SL2) (x : Cusp) :
    fractional Jm (cuspAct g x) = cuspAct (conjJ g) (fractional Jm x) := by
  rw [← frac_eq_cuspAct, ← frac_eq_cuspAct, conjJ_val]
  show fractional !![(-1 : ℤ), 0; 0, 1] (fractional (g : Matrix (Fin 2) (Fin 2) ℤ) x) = _
  rw [frac_upper_comp, frac_comp_J, mul_assoc, mul_assoc, Jm_mul_Jm, mul_one]

/-! ### The reflection preserves the space of classes -/

variable {R : Type*} [CommRing R] {n : ℕ}

theorem act_mem_sym (A : Matrix (Fin 2) (Fin 2) ℤ) {P : Binary R}
    (hP : P ∈ MTT.Cohomology.Sym R n) : act A P ∈ MTT.Cohomology.Sym R n := by
  rw [MvPolynomial.mem_homogeneousSubmodule] at hP ⊢
  have hg : ∀ i : Fin 2,
      (∑ a : Fin 2, (A a i : R) • MvPolynomial.X a : Binary R).IsHomogeneous 1 := by
    intro i
    have hmem : (∑ a : Fin 2, (A a i : R) • MvPolynomial.X a : Binary R)
        ∈ MvPolynomial.homogeneousSubmodule (Fin 2) R 1 :=
      Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _
        (by rw [MvPolynomial.mem_homogeneousSubmodule]; exact MvPolynomial.isHomogeneous_X _ _)
    exact hmem
  have h := hP.aeval (g := fun i : Fin 2 =>
    (∑ a : Fin 2, (A a i : R) • MvPolynomial.X a : Binary R)) hg
  rw [one_mul] at h
  exact h

end P2MRC

namespace P2MRC

open MvPolynomial P2MSE

variable {R : Type*} [CommRing R] {N n : ℕ}

theorem conjJ_entries (g : SL2) :
    (conjJ g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 ∧
    (conjJ g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = -(g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ∧
    (conjJ g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [conjJ_val, Jm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul,
      Matrix.vecHead, Matrix.vecTail]

theorem conjJ_mem_Gamma1 {g : SL2} (hg : g ∈ CongruenceSubgroup.Gamma1 N) :
    conjJ g ∈ CongruenceSubgroup.Gamma1 N := by
  obtain ⟨h00, h10, h11⟩ := conjJ_entries g
  rw [CongruenceSubgroup.Gamma1_mem] at hg ⊢
  refine ⟨by rw [h00]; exact hg.1, by rw [h11]; exact hg.2.1, ?_⟩
  rw [h10]
  push_cast
  rw [hg.2.2, neg_zero]

theorem conjJ_mem_Gamma0 {g : SL2} (hg : g ∈ CongruenceSubgroup.Gamma0 N) :
    conjJ g ∈ CongruenceSubgroup.Gamma0 N := by
  obtain ⟨-, h10, -⟩ := conjJ_entries g
  rw [CongruenceSubgroup.Gamma0_mem] at hg ⊢
  rw [h10]
  push_cast
  rw [hg, neg_zero]

/-- The key conjugation identity on the coefficient action. -/
theorem act_conj (g : SL2) (P : Binary R) :
    act Jm (act (conjJ g : Matrix (Fin 2) (Fin 2) ℤ) P)
      = act ((g : Matrix (Fin 2) (Fin 2) ℤ) * Jm) P := by
  rw [← act_mul, conjJ_val, ← mul_assoc, ← mul_assoc, Jm_mul_Jm, one_mul]

/-- The reflection of a class is a class. -/
theorem reflection_mem (φ : Hc N n R) : reflection φ.val ∈ Hc N n R := by
  refine ⟨fun x y => ?_, fun x y z => ?_, fun γ x y => ?_⟩
  · exact act_mem_sym _ (φ.2.1 _ _)
  · show act Jm _ + act Jm _ = act Jm _
    rw [← map_add]
    exact congrArg _ (φ.2.2.1 _ _ _)
  · show act Jm (φ.val (fractional Jm (cuspAct γ.val x), fractional Jm (cuspAct γ.val y)))
      = act (γ.val : Matrix (Fin 2) (Fin 2) ℤ)
          (act Jm (φ.val (fractional Jm x, fractional Jm y)))
    rw [frac_J_cuspAct, frac_J_cuspAct,
      φ.2.2.2 ⟨conjJ γ.val, conjJ_mem_Gamma1 γ.2⟩ (fractional Jm x) (fractional Jm y),
      act_conj, act_mul]

/-- The reflection preserves the nebentype law. -/
theorem reflection_char (φ : Hc N n R) (e : ZMod N → R)
    (h : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      φ.val (cuspAct γ.val x, cuspAct γ.val y)
        = e ((γ.val : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod N) •
          act (γ.val : Matrix (Fin 2) (Fin 2) ℤ) (φ.val (x, y)))
    (γ : CongruenceSubgroup.Gamma0 N) (x y : Cusp) :
    reflection φ.val (cuspAct γ.val x, cuspAct γ.val y)
      = e ((γ.val : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod N) •
        act (γ.val : Matrix (Fin 2) (Fin 2) ℤ) (reflection φ.val (x, y)) := by
  obtain ⟨-, -, h11⟩ := conjJ_entries γ.val
  show act Jm (φ.val (fractional Jm (cuspAct γ.val x), fractional Jm (cuspAct γ.val y)))
    = _ • act (γ.val : Matrix (Fin 2) (Fin 2) ℤ)
        (act Jm (φ.val (fractional Jm x, fractional Jm y)))
  rw [frac_J_cuspAct, frac_J_cuspAct,
    h ⟨conjJ γ.val, conjJ_mem_Gamma0 γ.2⟩ (fractional Jm x) (fractional Jm y),
    h11, map_smul, act_conj, act_mul]

end P2MRC

namespace P2MRC

open MvPolynomial P2MSE

variable {R : Type*} [CommRing R] {N n : ℕ}

/-- The unipotent matrices, all of which lie in `Γ₁(N)`. -/
abbrev Um (t : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, t; 0, 1]

def USL (t : ℤ) : SL2 := ⟨Um t, by simp [Um, Matrix.det_fin_two_of]⟩

theorem USL_val (t : ℤ) : ((USL t : SL2) : Matrix (Fin 2) (Fin 2) ℤ) = Um t := rfl

theorem USL_mem (N : ℕ) (t : ℤ) : USL t ∈ CongruenceSubgroup.Gamma1 N := by
  rw [CongruenceSubgroup.Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩ <;> simp [USL_val, Um]

theorem frac_J_comp (g : Matrix (Fin 2) (Fin 2) ℤ) (x : Cusp) :
    fractional Jm (fractional g x) = fractional (Jm * g) x :=
  frac_upper_comp (-1) 0 g x

theorem frac_U_comp (t : ℤ) (g : Matrix (Fin 2) (Fin 2) ℤ) (x : Cusp) :
    fractional (Um t) (fractional g x) = fractional (Um t * g) x :=
  frac_upper_comp 1 t g x

/-- The reflection turns the slash operator by `A` into the one by `A'`, provided the two
conjugation identities hold with a unipotent correction `Um t ∈ Γ₁(N)`. -/
theorem slash_refl_key (φ : Hc N n R) (t : ℤ) (A A' : Matrix (Fin 2) (Fin 2) ℤ)
    (h1 : A * Jm = Um t * (Jm * A'))
    (h2 : Jm * A.adjugate * Um t = A'.adjugate * Jm) :
    reflection (slash A φ.val) = slash A' (reflection φ.val) := by
  funext D
  have hcusp : ∀ x : Cusp, fractional A (fractional Jm x)
      = cuspAct (USL t) (fractional (Jm * A') x) := by
    intro x
    rw [frac_comp_J, h1, ← frac_U_comp, ← frac_eq_cuspAct, USL_val]
  show act Jm (act A.adjugate (φ.val (fractional A (fractional Jm D.1),
      fractional A (fractional Jm D.2))))
    = act A'.adjugate (act Jm (φ.val (fractional Jm (fractional A' D.1),
      fractional Jm (fractional A' D.2))))
  rw [hcusp, hcusp, φ.2.2.2 ⟨USL t, USL_mem N t⟩ _ _]
  show act Jm (act A.adjugate (act (Um t) _)) = _
  rw [← act_mul, ← act_mul, h2, act_mul, frac_J_comp, frac_J_comp]

/-! ### The reindexing of the Hecke coset representatives -/

def sigmaFin (l : ℕ) (b : Fin l) : Fin l :=
  ⟨if b.val = 0 then 0 else l - b.val, by
    have hb := b.isLt
    split <;> omega⟩

theorem sigmaFin_val (l : ℕ) (b : Fin l) :
    (sigmaFin l b).val = if b.val = 0 then 0 else l - b.val := rfl

theorem sigmaFin_involutive (l : ℕ) : Function.Involutive (sigmaFin l) := by
  intro b
  have hb := b.isLt
  apply Fin.ext
  rw [sigmaFin_val, sigmaFin_val]
  by_cases h : b.val = 0
  · simp [h]
  · rw [ite_eq_right h, ite_eq_right (by omega : ¬ (l - b.val = 0))]
    omega

def sigmaEquiv (l : ℕ) : Fin l ≃ Fin l :=
  Function.Involutive.toPerm _ (sigmaFin_involutive l)

end P2MRC

namespace P2MRC

open MvPolynomial P2MSE

variable {R : Type*} [CommRing R] {N n : ℕ}

theorem reflection_zero : reflection (0 : (Cusp × Cusp) → Binary R) = 0 := by
  funext D; show act Jm 0 = 0; rw [map_zero]

theorem reflection_sum {ι : Type*} (s : Finset ι) (f : ι → (Cusp × Cusp) → Binary R) :
    reflection (∑ b ∈ s, f b) = ∑ b ∈ s, reflection (f b) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, reflection_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, reflection_add, ih]

/-! ### The three coset identities -/

theorem refl_slash_b (φ : Hc N n R) (l : ℕ) (b : Fin l) :
    reflection (slash !![1, (b.val : ℤ); 0, (l : ℤ)] φ.val)
      = slash !![1, ((sigmaFin l b).val : ℤ); 0, (l : ℤ)] (reflection φ.val) := by
  by_cases h : b.val = 0
  · have hb0 : ((b.val : ℕ) : ℤ) = 0 := by rw [h]; rfl
    have hs0 : (((sigmaFin l b).val : ℕ) : ℤ) = 0 := by
      rw [sigmaFin_val, ite_eq_left h]; rfl
    rw [hb0, hs0]
    refine slash_refl_key φ 0 _ _ ?_ ?_ <;>
      (ext i j; fin_cases i <;> fin_cases j <;>
        simp [Jm, Um, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two_of])
  · have hs : (((sigmaFin l b).val : ℕ) : ℤ) = (l : ℤ) - ((b.val : ℕ) : ℤ) := by
      rw [sigmaFin_val, ite_eq_right h]
      have hb := b.isLt
      omega
    rw [hs]
    refine slash_refl_key φ 1 _ _ ?_ ?_ <;>
      (ext i j; fin_cases i <;> fin_cases j <;>
        simp [Jm, Um, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two_of] <;> ring)

theorem refl_slash_diag (φ : Hc N n R) (l : ℕ) :
    reflection (slash !![(l : ℤ), 0; 0, 1] φ.val)
      = slash !![(l : ℤ), 0; 0, 1] (reflection φ.val) := by
  refine slash_refl_key φ 0 _ _ ?_ ?_ <;>
    (ext i j; fin_cases i <;> fin_cases j <;>
      simp [Jm, Um, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two_of])

/-- The reflection commutes with the prime Hecke operator. -/
theorem reflection_primeHecke (e : R) (l : ℕ) (φ : Hc N n R) :
    reflection (primeHecke e l φ.val) = primeHecke e l (reflection φ.val) := by
  have hsum : (∑ b : Fin l, reflection (slash !![1, (b.val : ℤ); 0, (l : ℤ)] φ.val))
      = ∑ b : Fin l, slash !![1, (b.val : ℤ); 0, (l : ℤ)] (reflection φ.val) :=
    Fintype.sum_equiv (sigmaEquiv l) _ _ (fun b => refl_slash_b φ l b)
  simp only [primeHecke]
  rw [reflection_add, reflection_smul, reflection_sum, refl_slash_diag, hsum]

end P2MRC

open P2MRC in
theorem solution {N n : ℕ} {R : Type*} [CommRing R] (φ : Hc N n R) :
    (∃ ψ : Hc N n R, ψ.val = reflection φ.val) ∧
    (∀ (e : R) (l : ℕ), reflection (primeHecke e l φ.val)
        = primeHecke e l (reflection φ.val)) ∧
    (∀ (e : ZMod N → R),
      (∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
        φ.val (cuspAct γ.val x, cuspAct γ.val y)
          = e (γ.val 1 1 : ZMod N) • act γ.val.val (φ.val (x, y))) →
      ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
        reflection φ.val (cuspAct γ.val x, cuspAct γ.val y)
          = e (γ.val 1 1 : ZMod N) • act γ.val.val (reflection φ.val (x, y))) :=
  ⟨⟨⟨reflection φ.val, reflection_mem φ⟩, rfl⟩,
   fun e l => reflection_primeHecke e l φ,
   fun e h γ x y => reflection_char φ e h γ x y⟩
end

end privateSection

public section publicSection

noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.reflection_class {N n : ℕ} {R : Type*} [CommRing R] (φ : Hc N n R) :
    (∃ ψ : Hc N n R, ψ.val = reflection φ.val) ∧
    (∀ (e : R) (l : ℕ), reflection (primeHecke e l φ.val)
        = primeHecke e l (reflection φ.val)) ∧
    (∀ (e : ZMod N → R),
      (∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
        φ.val (cuspAct γ.val x, cuspAct γ.val y)
          = e (γ.val 1 1 : ZMod N) • act γ.val.val (φ.val (x, y))) →
      ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
        reflection φ.val (cuspAct γ.val x, cuspAct γ.val y)
          = e (γ.val 1 1 : ZMod N) • act γ.val.val (reflection φ.val (x, y))) := _root_.solution φ
end

end publicSection
