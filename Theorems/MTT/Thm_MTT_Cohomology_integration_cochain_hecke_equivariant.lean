/-
Based on Prove2Me node MTT.Cohomology.integration_cochain_hecke_equivariant
(60992b0d-f0d1-40f8-8df3-157cbfcc3d7a) by davidloeffler (2026-09-06).

Proof based on Prove2Me submission 1bacf9ce-46d7-4a42-95d4-6967c690e87a
by cbirkbeck (2026-09-06); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import Definitions.MTT.Def_MTT_Cohomology_Integration
public import Mathlib.RingTheory.Flat.Basic

import Mathlib.NumberTheory.ModularForms.LFunction
import Mathlib.NumberTheory.ModularForms.Identities

/-!
# Hecke equivariance of cusp-to-cusp integration

Theorem statement: `MTT.Cohomology.integration_cochain_hecke_equivariant`
(`60992b0d-f0d1-40f8-8df3-157cbfcc3d7a`), by davidloeffler, 2026-09-06.

Proof: submission `1bacf9ce-46d7-4a42-95d4-6967c690e87a`, by cbirkbeck, 2026-09-06 (ACCEPTED);
locally adapted.

Let $N>0$ and $k\ge 2$. The cusp-to-cusp integration map

$$
I:S_k(\Gamma_1(N))\longrightarrow H_c(N,k-2;\mathbf C)
$$

intertwines the analytic and modular-symbol prime Hecke operators. Explicitly, for every Dirichlet
character $e$ modulo $N$, every prime $\ell$ (including primes dividing $N$), and every cusp form
$f$, integrating the analytic transform $T_{\ell,e}f$ gives the modular-symbol transform
$T_{\ell,e}I(f)$, with the normalizations fixed in the cohomology definitions.

## Explanation of the source proof

We prove that the integration cochain is Hecke-equivariant in the mission's sense: if $g=T_\ell f$
pointwise, where
$$(T_\ell f)(z)=\frac1\ell\sum_{b=0}^{\ell-1}f\Big(\frac{z+b}{\ell}\Big)+e\,\ell^{k-1}f(\ell
z)\qquad(e=\varepsilon(\ell)),$$
then $\Phi_g=T_\ell\Phi_f$ on cochains, where $T_\ell\phi=\sum_b\phi|\beta_b+e\,\phi|\alpha$ with
$\beta_b=\begin{pmatrix}1&b\\0&\ell\end{pmatrix}$, $\alpha=\begin{pmatrix}\ell&0\\0&1\end{pmatrix}$
and $(\phi|M)(x,y)=\operatorname{adj}(M)\cdot\phi(Mx,My)$. Recall $\Phi_f(x,y)=P_f(y)-P_f(x)$ with
$P_f(\infty)=0$ and, for $r\in\mathbf Q$,
$$P_f(r)=\sum_{j=0}^{n}\binom nj\Lambda_{f,r}(z^j)\,X^jY^{n-j},\qquad
\Lambda_{f,r}(Q)=2\pi\int_0^\infty f(r+it)\,Q(r+it)\,dt,\quad n=k-2 .$$
Since $\operatorname{adj}(M)\cdot$ is linear and the matrices $\beta_b,\alpha$ fix $\infty$, it
suffices to prove the primitive-level identity $P_g(r)=\sum_b\operatorname{adj}(\beta_b)\cdot
P_f(\tfrac{r+b}{\ell})+e\,\operatorname{adj}(\alpha)\cdot P_f(\ell r)$ for $r\in\mathbf Q$
(`cuspPeriodPolynomial_heckePrime`), the case of $\infty$ being trivial
(`integrationCochain_heckePrime`).

**Analysis.** For a cusp form $f$ on $\Gamma_1(N)$ and every $r\in\mathbf Q$ the functions $t\mapsto
f(r+it)t^j$ are integrable on $(0,\infty)$ (`rational_translate_integrable`, taken from the accepted
proof of `MTT.birch_mellin_formula`: it comes from Mathlib's strong functional-equation pair of the
translated cusp form). Hence $\Lambda_{f,r}$ is a well-defined linear functional on $\mathbf C[z]$
(`Lam`). The substitution $t=\ell s$ gives, for every polynomial $Q$,
$$\Lambda_{f((\cdot+b)/\ell),\,r}(Q)=\ell\,\Lambda_{f,\frac{r+b}{\ell}}\big(Q(\ell z-b)\big),\qquad
\Lambda_{f(\ell\,\cdot),\,r}(Q)=\ell^{-1}\Lambda_{f,\ell r}\big(Q(z/\ell)\big)$$
(`modularIntegral_upTranslate`, `modularIntegral_scaleTranslate`, via `integral_comp_mul_left_Ioi`),
and integrability transfers along the same substitution (`GoodAt.upTranslate`,
`GoodAt.scaleTranslate`). Splitting the integrand of $\Lambda_{g,r}$ according to the definition of
$T_\ell f$ and using linearity of the integral (which is where integrability is needed) yields the
identity of linear functionals
$$\Lambda_{g,r}=\sum_{b}\Lambda_{f,\frac{r+b}{\ell}}\circ c_{\ell
z-b}+e\,\ell^{k-2}\,\Lambda_{f,\ell r}\circ c_{z/\ell},\qquad c_q(Q)=Q\circ q$$
(`modularIntegral_heckePrime`, `Lam_heckePrime`).

**Algebra.** Write $\widehat\Lambda$ for the coefficientwise application of a functional $\Lambda$
to a polynomial in $X,Y$ with coefficients in $\mathbf C[z]$ (`hat`); then
$P_f(r)=\widehat{\Lambda_{f,r}}\big((zX+Y)^n\big)$ (`hat_kernel`, `cuspPeriodPolynomial_eq_hat`).
Two formal properties drive the computation: $\widehat{\Lambda\circ
c_q}(R)=\widehat\Lambda(R|_{z\mapsto q})$ (`hat_comp`), and $\widehat\Lambda$ commutes with the
coefficient action $\gamma\cdot$, applied over $\mathbf C[z]$ on one side and over $\mathbf C$ on
the other (`hat_act'`, proved by induction on the polynomial since the substitution has integer
coefficients). Now $\operatorname{adj}(\beta_b)=\begin{pmatrix}\ell&-b\\0&1\end{pmatrix}$ sends
$(X,Y)\mapsto(\ell X,\,Y-bX)$, so $\operatorname{adj}(\beta_b)\cdot(zX+Y)^n=((\ell
z-b)X+Y)^n=(zX+Y)^n|_{z\mapsto\ell z-b}$ (`act'_kernel_β`), while
$\operatorname{adj}(\alpha)=\operatorname{diag}(1,\ell)$ gives $(zX+\ell
Y)^n=\ell^n\,(zX+Y)^n|_{z\mapsto z/\ell}$ (`act'_kernel_α`). Applying $\widehat{\ }$ to the identity
of functionals above therefore gives
$$P_g(r)=\sum_b\operatorname{adj}(\beta_b)\cdot
P_f\big(\tfrac{r+b}{\ell}\big)+e\,\ell^{k-2}\ell^{-n}\operatorname{adj}(\alpha)\cdot P_f(\ell r),$$
and $\ell^{k-2}\ell^{-n}=1$. This is the classical statement that the modular-symbol map intertwines
$T_\ell$ on cusp forms with the Hecke operator on $\operatorname{Sym}^{k-2}$-valued modular symbols
(Merel, *Universal Fourier expansions of modular forms*, §1; Stevens, *Arithmetic on modular
curves*, Ch. 2), specialised to the mission's normalisations.

<!-- Generated by add_prove2me_provenance.py -->
-/

section privateSection

noncomputable section
open scoped BigOperators ModularForm TensorProduct
open MeasureTheory MatrixGroups Complex UpperHalfPlane
open MTT MTT.Cohomology ModularForm
open ConjAct Pointwise

namespace MTT.HeckeEquiv

/-! ### Part A: integrability, the vertical integrals, and the substitution `t ↦ lt` -/

lemma rational_translate_integrable
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (f : CuspForm (GammaOne N) (k : ℤ)) (r : ℚ) (j : ℕ) :
    IntegrableOn (fun t : ℝ =>
      f (ofComplex ((r : ℂ) + Complex.I * t)) * (t : ℂ)^j) (Set.Ioi 0) := by
  let : NeZero N := ⟨by omega⟩
  let g : GL (Fin 2) ℚ := Matrix.GeneralLinearGroup.upperRightHom r
  let gr : GL (Fin 2) ℝ := g.map (Rat.castHom ℝ)
  have hr : gr = Matrix.GeneralLinearGroup.upperRightHom (r : ℝ) := by
    ext i l
    fin_cases i <;> fin_cases l <;> simp [gr, g]
  let : (GammaOne N).IsArithmetic := by dsimp [GammaOne]; infer_instance
  let : (toConjAct gr⁻¹ • GammaOne N).IsArithmetic := by
    have hh := Subgroup.IsArithmetic.conj (GammaOne N) g⁻¹
    simpa [gr] using hh
  let F := CuspForm.translate f gr
  have hconv := ((CuspForm.isStrongFEPair (by omega : (0 : ℤ) < k) F).hasMellin
    ((j : ℂ)+1)).1
  unfold MellinConvergent at hconv
  have hval (t : ℝ) (ht : 0 < t) :
      F (ofComplex (Complex.I * t)) = f (ofComplex ((r : ℂ) + Complex.I * t)) := by
    change (⇑f ∣[(k : ℤ)] gr) _ = _
    rw [slash_def, hr]
    simp only [Matrix.GeneralLinearGroup.val_det_apply]
    simp [σ, denom, Matrix.GeneralLinearGroup.upperRightHom]
    congr 1
    ext
    simp [coe_smul, σ, num, denom, ofComplex_apply_of_im_pos, ht]
    ring
  apply hconv.congr_fun _ measurableSet_Ioi
  intro t ht
  simp only [ModularForm.weakFEPair, add_sub_cancel_right, Complex.cpow_natCast,
    smul_eq_mul, hval t ht]
  ring

/-- The integrand `t ↦ F(r+it) P(r+it)` of the modular integral. -/
def vint (F : ℍ → ℂ) (P : Polynomial ℂ) (r : ℚ) (t : ℝ) : ℂ :=
  F (ofComplex ((r : ℂ) + Complex.I * t)) * P.eval ((r : ℂ) + Complex.I * t)

lemma modularIntegral_eq (F : ℍ → ℂ) (P : Polynomial ℂ) (r : ℚ) :
    modularIntegral F P r = (2 * Real.pi : ℂ) * ∫ t in Set.Ioi (0 : ℝ), vint F P r t := rfl

/-- Integrability of `t ↦ F(r+it) t^j` on `(0,∞)` for all `j`. -/
def GoodAt (F : ℍ → ℂ) (r : ℚ) : Prop :=
  ∀ j : ℕ, IntegrableOn (fun t : ℝ => F (ofComplex ((r : ℂ) + Complex.I * t)) * (t : ℂ) ^ j)
    (Set.Ioi 0)

lemma goodAt_of_cuspForm {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (f : CuspForm (GammaOne N) (k : ℤ)) (r : ℚ) : GoodAt f r :=
  fun j => rational_translate_integrable hN hk f r j

lemma GoodAt.pow {F : ℍ → ℂ} {r : ℚ} (h : GoodAt F r) (n : ℕ) :
    IntegrableOn (fun t : ℝ => F (ofComplex ((r : ℂ) + Complex.I * t)) *
      ((r : ℂ) + Complex.I * t) ^ n) (Set.Ioi 0) := by
  have : (fun t : ℝ => F (ofComplex ((r : ℂ) + Complex.I * t)) * ((r : ℂ) + Complex.I * t) ^ n) =
      fun t : ℝ => ∑ m ∈ Finset.range (n + 1),
        ((r : ℂ) ^ m * Complex.I ^ (n - m) * (n.choose m : ℂ)) *
          (F (ofComplex ((r : ℂ) + Complex.I * t)) * (t : ℂ) ^ (n - m)) := by
    funext t
    rw [add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_pow]; ring
  rw [this]
  exact integrable_finsetSum _ fun m _ => (h (n - m)).const_mul _

lemma GoodAt.integrable_vint {F : ℍ → ℂ} {r : ℚ} (h : GoodAt F r) (P : Polynomial ℂ) :
    IntegrableOn (vint F P r) (Set.Ioi 0) := by
  have : vint F P r = fun t : ℝ => ∑ i ∈ Finset.range (P.natDegree + 1),
      P.coeff i * (F (ofComplex ((r : ℂ) + Complex.I * t)) * ((r : ℂ) + Complex.I * t) ^ i) := by
    funext t
    simp only [vint, Polynomial.eval_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [this]
  exact integrable_finsetSum _ fun i _ => (h.pow i).const_mul _

lemma GoodAt.modularIntegral_add {F : ℍ → ℂ} {r : ℚ} (h : GoodAt F r) (P Q : Polynomial ℂ) :
    modularIntegral F (P + Q) r = modularIntegral F P r + modularIntegral F Q r := by
  simp only [modularIntegral_eq]
  rw [← mul_add, ← integral_add (h.integrable_vint P) (h.integrable_vint Q)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [vint, Polynomial.eval_add]
  ring

lemma GoodAt.modularIntegral_smul {F : ℍ → ℂ} {r : ℚ} (_h : GoodAt F r) (c : ℂ)
    (P : Polynomial ℂ) :
    modularIntegral F (c • P) r = c * modularIntegral F P r := by
  simp only [modularIntegral_eq]
  have : ∫ t in Set.Ioi (0 : ℝ), vint F (c • P) r t = c * ∫ t in Set.Ioi (0 : ℝ), vint F P r t := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi fun t _ => ?_
    simp only [vint, Polynomial.eval_smul, smul_eq_mul]
    ring
  rw [this]; ring

/-- The vertical integral as a linear functional on polynomials. -/
def Lam (F : ℍ → ℂ) (r : ℚ) (h : GoodAt F r) : Polynomial ℂ →ₗ[ℂ] ℂ where
  toFun P := modularIntegral F P r
  map_add' P Q := h.modularIntegral_add P Q
  map_smul' c P := by simp only [RingHom.id_apply]; exact h.modularIntegral_smul c P

@[simp] lemma Lam_apply (F : ℍ → ℂ) (r : ℚ) (h : GoodAt F r) (P : Polynomial ℂ) :
    Lam F r h P = modularIntegral F P r := rfl

/-! #### The translates `z ↦ (z + b)/l` and `z ↦ l z` -/

lemma coe_ofComplex_of_pos (r : ℚ) {t : ℝ} (ht : 0 < t) :
    ((ofComplex ((r : ℂ) + Complex.I * t) : ℍ) : ℂ) = (r : ℂ) + Complex.I * t := by
  rw [ofComplex_apply_of_im_pos (by simpa using ht)]

/-- `F((z+b)/l)`. -/
def upTranslate (l b : ℕ) (F : ℍ → ℂ) : ℍ → ℂ :=
  fun z => F (ofComplex (((z : ℂ) + (b : ℂ)) / (l : ℂ)))

/-- `F(l z)`. -/
def scaleTranslate (l : ℕ) (F : ℍ → ℂ) : ℍ → ℂ :=
  fun z => F (ofComplex ((l : ℂ) * (z : ℂ)))

lemma ofComplex_shift_div {l : ℕ} (hl : 0 < l) (r : ℚ) (b : ℕ) (t : ℝ) :
    ((((r : ℂ) + Complex.I * t) + (b : ℂ)) / (l : ℂ)) =
      (((r + b) / l : ℚ) : ℂ) + Complex.I * ((l : ℝ)⁻¹ * t : ℝ) := by
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  push_cast
  field_simp
  ring

/-- Substitution `t = l s` in the vertical integral of an up-translate. -/
lemma modularIntegral_upTranslate {l : ℕ} (hl : 0 < l) (b : ℕ) (F : ℍ → ℂ) (P : Polynomial ℂ)
    (r : ℚ) :
    modularIntegral (upTranslate l b F) P r =
      (l : ℂ) * modularIntegral F (P.comp (Polynomial.C (l : ℂ) * Polynomial.X - Polynomial.C (b : ℂ)))
        ((r + b) / l) := by
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have hlR : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hl)
  simp only [modularIntegral_eq]
  set G : ℝ → ℂ := vint F (P.comp (Polynomial.C (l : ℂ) * Polynomial.X - Polynomial.C (b : ℂ)))
    ((r + b) / l) with hG
  have hpt : ∀ t : ℝ, 0 < t → vint (upTranslate l b F) P r t = G ((l : ℝ)⁻¹ * t) := by
    intro t ht
    simp only [hG, vint, upTranslate, Polynomial.eval_comp, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    rw [coe_ofComplex_of_pos r ht, ofComplex_shift_div hl r b t]
    congr 1
    push_cast
    field_simp
    all_goals ring_nf
  have h1 : ∫ t in Set.Ioi (0 : ℝ), vint (upTranslate l b F) P r t =
      ∫ t in Set.Ioi (0 : ℝ), G ((l : ℝ)⁻¹ * t) :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht => hpt t ht
  rw [h1, integral_comp_mul_left_Ioi G 0 hlR, mul_zero, inv_inv, Complex.real_smul]
  push_cast
  all_goals ring

lemma ofComplex_scale {l : ℕ} (r : ℚ) (t : ℝ) :
    (l : ℂ) * ((r : ℂ) + Complex.I * t) = ((l * r : ℚ) : ℂ) + Complex.I * ((l : ℝ) * t : ℝ) := by
  push_cast; ring

/-- Substitution `t = s / l` in the vertical integral of a scale-translate. -/
lemma modularIntegral_scaleTranslate {l : ℕ} (hl : 0 < l) (F : ℍ → ℂ) (P : Polynomial ℂ) (r : ℚ) :
    modularIntegral (scaleTranslate l F) P r =
      (l : ℂ)⁻¹ * modularIntegral F (P.comp (Polynomial.C (l : ℂ)⁻¹ * Polynomial.X)) (l * r) := by
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl
  simp only [modularIntegral_eq]
  set G : ℝ → ℂ := vint F (P.comp (Polynomial.C (l : ℂ)⁻¹ * Polynomial.X)) (l * r) with hG
  have hpt : ∀ t : ℝ, 0 < t → vint (scaleTranslate l F) P r t = G ((l : ℝ) * t) := by
    intro t ht
    simp only [hG, vint, scaleTranslate, Polynomial.eval_comp,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    rw [coe_ofComplex_of_pos r ht, ofComplex_scale r t]
    congr 1
    push_cast
    field_simp
  have h1 : ∫ t in Set.Ioi (0 : ℝ), vint (scaleTranslate l F) P r t =
      ∫ t in Set.Ioi (0 : ℝ), G ((l : ℝ) * t) :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht => hpt t ht
  rw [h1, integral_comp_mul_left_Ioi G 0 hlR, mul_zero, Complex.real_smul]
  push_cast
  all_goals ring

/-- Integrability transfers to the up-translates. -/
lemma GoodAt.upTranslate {l : ℕ} (hl : 0 < l) (b : ℕ) {F : ℍ → ℂ} (r : ℚ)
    (h : GoodAt F ((r + b) / l)) : GoodAt (upTranslate l b F) r := by
  intro j
  have hlR : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hl)
  set H : ℝ → ℂ := fun s => F (ofComplex ((((r + b) / l : ℚ) : ℂ) + Complex.I * s)) *
    ((l : ℂ) ^ j * (s : ℂ) ^ j) with hH
  have hHint : IntegrableOn H (Set.Ioi 0) := by
    have h1 : IntegrableOn (fun s : ℝ => (l : ℂ) ^ j *
        (F (ofComplex ((((r + b) / l : ℚ) : ℂ) + Complex.I * s)) * (s : ℂ) ^ j)) (Set.Ioi 0) :=
      (h j).const_mul ((l : ℂ) ^ j)
    refine IntegrableOn.congr_fun h1 (fun s _ => ?_) measurableSet_Ioi
    simp only [hH]; ring
  have h2 : IntegrableOn (fun t : ℝ => H ((l : ℝ)⁻¹ * t)) (Set.Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff H 0 hlR).mpr (by simpa using hHint)
  refine IntegrableOn.congr_fun h2 (fun t ht => ?_) measurableSet_Ioi
  simp only [hH, HeckeEquiv.upTranslate]
  rw [coe_ofComplex_of_pos r ht, ofComplex_shift_div hl r b t]
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  congr 1
  push_cast
  rw [mul_pow, inv_pow, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hl'), one_mul]

/-- Integrability transfers to the scale-translates. -/
lemma GoodAt.scaleTranslate {l : ℕ} (hl : 0 < l) {F : ℍ → ℂ} (r : ℚ)
    (h : GoodAt F (l * r)) : GoodAt (scaleTranslate l F) r := by
  intro j
  have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  set H : ℝ → ℂ := fun s => F (ofComplex (((l * r : ℚ) : ℂ) + Complex.I * s)) *
    ((l : ℂ)⁻¹ ^ j * (s : ℂ) ^ j) with hH
  have hHint : IntegrableOn H (Set.Ioi 0) := by
    have h1 : IntegrableOn (fun s : ℝ => (l : ℂ)⁻¹ ^ j *
        (F (ofComplex (((l * r : ℚ) : ℂ) + Complex.I * s)) * (s : ℂ) ^ j)) (Set.Ioi 0) :=
      (h j).const_mul ((l : ℂ)⁻¹ ^ j)
    refine IntegrableOn.congr_fun h1 (fun s _ => ?_) measurableSet_Ioi
    simp only [hH]; ring
  have h2 : IntegrableOn (fun t : ℝ => H ((l : ℝ) * t)) (Set.Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff H 0 hlR).mpr (by simpa using hHint)
  refine IntegrableOn.congr_fun h2 (fun t ht => ?_) measurableSet_Ioi
  simp only [hH, HeckeEquiv.scaleTranslate]
  rw [coe_ofComplex_of_pos r ht, ofComplex_scale r t]
  congr 1
  push_cast
  rw [inv_pow, mul_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hl'), one_mul]

/-- The vertical integrals of `T_l f` decompose along the translates. -/
lemma modularIntegral_heckePrime {l : ℕ} (hl : 0 < l) (k : ℕ) (e : ℂ) (f g : ℍ → ℂ)
    (hg : ∀ z, g z = heckePrime k e l f z) (r : ℚ)
    (hf : ∀ b : ℕ, GoodAt f ((r + b) / l)) (hf' : GoodAt f (l * r)) (P : Polynomial ℂ) :
    modularIntegral g P r =
      ∑ b : Fin l, modularIntegral f
          (P.comp (Polynomial.C (l : ℂ) * Polynomial.X - Polynomial.C (b.val : ℂ))) ((r + b.val) / l) +
        e * (l : ℂ) ^ (k - 1) * (l : ℂ)⁻¹ *
          modularIntegral f (P.comp (Polynomial.C (l : ℂ)⁻¹ * Polynomial.X)) (l * r) := by
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have hup : ∀ b : Fin l, GoodAt (upTranslate l b.val f) r :=
    fun b => GoodAt.upTranslate hl b.val r (hf b.val)
  have hsc : GoodAt (scaleTranslate l f) r := GoodAt.scaleTranslate hl r hf'
  -- pointwise decomposition of the integrand
  have hpt : ∀ t : ℝ, vint g P r t =
      ∑ b : Fin l, (l : ℂ)⁻¹ * vint (upTranslate l b.val f) P r t +
        (e * (l : ℂ) ^ (k - 1)) * vint (scaleTranslate l f) P r t := by
    intro t
    simp only [vint, hg, heckePrime, upTranslate, scaleTranslate]
    rw [add_mul, mul_assoc ((l : ℂ)⁻¹), Finset.sum_mul (s := (Finset.univ : Finset (Fin l))),
      Finset.mul_sum (s := (Finset.univ : Finset (Fin l)))]
    ring
  have hint1 : ∀ b : Fin l, IntegrableOn (fun t => (l : ℂ)⁻¹ * vint (upTranslate l b.val f) P r t)
      (Set.Ioi 0) := fun b => ((hup b).integrable_vint P).const_mul _
  have hint2 : IntegrableOn (fun t => (e * (l : ℂ) ^ (k - 1)) * vint (scaleTranslate l f) P r t)
      (Set.Ioi 0) := (hsc.integrable_vint P).const_mul _
  rw [modularIntegral_eq, setIntegral_congr_fun measurableSet_Ioi (fun t _ => hpt t),
    integral_add (integrable_finsetSum _ fun b _ => hint1 b) hint2,
    integral_finsetSum _ fun b _ => hint1 b]
  simp only [integral_const_mul]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun b _ => ?_
    have := modularIntegral_upTranslate hl b.val f P r
    rw [modularIntegral_eq] at this
    rw [← mul_assoc, mul_comm (2 * Real.pi : ℂ), mul_assoc, this]
    field_simp
  · have := modularIntegral_scaleTranslate hl f P r
    rw [modularIntegral_eq] at this
    rw [← mul_assoc, mul_comm (2 * Real.pi : ℂ), mul_assoc, this]
    ring

/-! ### Part B: polynomial-valued integrals and the coefficient action -/

/-- Apply a linear functional to the coefficients of a polynomial with coefficients in `ℂ[z]`. -/
def hat (Λ : Polynomial ℂ →ₗ[ℂ] ℂ) (R : MvPolynomial (Fin 2) (Polynomial ℂ)) : Binary ℂ :=
  ∑ m ∈ R.support, MvPolynomial.monomial m (Λ (AddMonoidAlgebra.coeff R m))

lemma coeff_hat (Λ : Polynomial ℂ →ₗ[ℂ] ℂ) (R : MvPolynomial (Fin 2) (Polynomial ℂ))
    (m : Fin 2 →₀ ℕ) : AddMonoidAlgebra.coeff (hat Λ R) m = Λ (AddMonoidAlgebra.coeff R m) := by
  unfold hat
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp h, map_zero]

/-- `hat` as a `ℂ`-linear map. -/
def hatL (Λ : Polynomial ℂ →ₗ[ℂ] ℂ) : MvPolynomial (Fin 2) (Polynomial ℂ) →ₗ[ℂ] Binary ℂ where
  toFun := hat Λ
  map_add' R S := by
    ext m
    simp only [coeff_hat, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add]
  map_smul' c R := by
    ext m; simp only [coeff_hat, MvPolynomial.coeff_smul, map_smul, RingHom.id_apply]

@[simp] lemma hatL_apply (Λ : Polynomial ℂ →ₗ[ℂ] ℂ) (R) : hatL Λ R = hat Λ R := rfl

lemma hat_add (Λ : Polynomial ℂ →ₗ[ℂ] ℂ) (R S : MvPolynomial (Fin 2) (Polynomial ℂ)) :
    hat Λ (R + S) = hat Λ R + hat Λ S := (hatL Λ).map_add R S

lemma hat_add_left (Λ₁ Λ₂ : Polynomial ℂ →ₗ[ℂ] ℂ) (R) :
    hat (Λ₁ + Λ₂) R = hat Λ₁ R + hat Λ₂ R := by
  ext m
  simp only [coeff_hat, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, LinearMap.add_apply]

lemma hat_smul_left (c : ℂ) (Λ : Polynomial ℂ →ₗ[ℂ] ℂ) (R) :
    hat (c • Λ) R = c • hat Λ R := by
  ext m; simp only [coeff_hat, MvPolynomial.coeff_smul, LinearMap.smul_apply]

lemma hat_sum_left {ι : Type*} (s : Finset ι) (Λ : ι → Polynomial ℂ →ₗ[ℂ] ℂ) (R) :
    hat (∑ i ∈ s, Λ i) R = ∑ i ∈ s, hat (Λ i) R := by
  ext m; simp only [coeff_hat, MvPolynomial.coeff_sum, LinearMap.sum_apply]

lemma hat_monomial (Λ : Polynomial ℂ →ₗ[ℂ] ℂ) (m : Fin 2 →₀ ℕ) (a : Polynomial ℂ) :
    hat Λ (MvPolynomial.monomial m a) = MvPolynomial.monomial m (Λ a) := by
  ext m'; simp only [coeff_hat, MvPolynomial.coeff_monomial]
  split_ifs <;> simp

lemma hat_C (Λ : Polynomial ℂ →ₗ[ℂ] ℂ) (a : Polynomial ℂ) :
    hat Λ (MvPolynomial.C a) = MvPolynomial.C (Λ a) := by
  rw [MvPolynomial.C_apply, hat_monomial, MvPolynomial.C_apply]

lemma hat_mul_X (Λ : Polynomial ℂ →ₗ[ℂ] ℂ) (R) (i : Fin 2) :
    hat Λ (R * MvPolynomial.X i) = hat Λ R * MvPolynomial.X i := by
  ext m; simp only [coeff_hat, MvPolynomial.coeff_mul_X']
  split_ifs <;> simp

lemma hat_intCast_smul (Λ : Polynomial ℂ →ₗ[ℂ] ℂ) (c : ℤ) (R) :
    hat Λ ((c : Polynomial ℂ) • R) = (c : ℂ) • hat Λ R := by
  ext m
  simp only [coeff_hat, MvPolynomial.coeff_smul, smul_eq_mul]
  rw [← Polynomial.C_eq_intCast, ← Polynomial.smul_eq_C_mul, map_smul, smul_eq_mul]

lemma hat_C_C_mul (Λ : Polynomial ℂ →ₗ[ℂ] ℂ) (c : ℂ) (R) :
    hat Λ (MvPolynomial.C (Polynomial.C c) * R) = c • hat Λ R := by
  ext m
  simp only [coeff_hat, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_smul, smul_eq_mul]
  rw [← Polynomial.smul_eq_C_mul, map_smul, smul_eq_mul]

/-- The coefficient action, over `ℂ[z]`. -/
def act' (γ : Matrix (Fin 2) (Fin 2) ℤ) :
    MvPolynomial (Fin 2) (Polynomial ℂ) →ₐ[Polynomial ℂ] MvPolynomial (Fin 2) (Polynomial ℂ) :=
  MvPolynomial.aeval fun i : Fin 2 => ∑ a : Fin 2, ((γ a i : ℤ) : Polynomial ℂ) • MvPolynomial.X a

lemma act'_X (γ : Matrix (Fin 2) (Fin 2) ℤ) (i : Fin 2) :
    act' γ (MvPolynomial.X i) = ∑ a : Fin 2, ((γ a i : ℤ) : Polynomial ℂ) • MvPolynomial.X a :=
  MvPolynomial.aeval_X _ _

lemma act'_C (γ : Matrix (Fin 2) (Fin 2) ℤ) (a : Polynomial ℂ) :
    act' γ (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [act', MvPolynomial.algebraMap_eq]

/-- The substitution underlying `act`, with its target algebra made explicit. -/
def actAlg (γ : Matrix (Fin 2) (Fin 2) ℤ) : Binary ℂ →ₐ[ℂ] Binary ℂ :=
  @MvPolynomial.aeval ℂ (Binary ℂ) (Fin 2) _ _ _
    (fun i : Fin 2 => ∑ a : Fin 2, ((γ a i : ℤ) : ℂ) • (MvPolynomial.X a : Binary ℂ))

lemma act_eq_actAlg (γ : Matrix (Fin 2) (Fin 2) ℤ) (P : Binary ℂ) : act γ P = actAlg γ P := rfl

lemma act_X (γ : Matrix (Fin 2) (Fin 2) ℤ) (i : Fin 2) :
    act γ (MvPolynomial.X i : Binary ℂ) =
      ∑ a : Fin 2, ((γ a i : ℤ) : ℂ) • (MvPolynomial.X a : Binary ℂ) := by
  rw [act_eq_actAlg]; simp [actAlg]

lemma act_C (γ : Matrix (Fin 2) (Fin 2) ℤ) (c : ℂ) : act γ (MvPolynomial.C c) = MvPolynomial.C c := by
  rw [act_eq_actAlg]; simp [actAlg]

lemma act_mul (γ : Matrix (Fin 2) (Fin 2) ℤ) (P Q : Binary ℂ) : act γ (P * Q) = act γ P * act γ Q := by
  rw [act_eq_actAlg, act_eq_actAlg, act_eq_actAlg, map_mul]

/-- `hat` intertwines the two coefficient actions. -/
lemma hat_act' (Λ : Polynomial ℂ →ₗ[ℂ] ℂ) (γ : Matrix (Fin 2) (Fin 2) ℤ)
    (R : MvPolynomial (Fin 2) (Polynomial ℂ)) : hat Λ (act' γ R) = act γ (hat Λ R) := by
  induction R using MvPolynomial.induction_on with
  | C a => rw [act'_C, hat_C, act_C]
  | add p q hp hq => rw [map_add, hat_add, hp, hq, hat_add, map_add]
  | mul_X p i hp =>
    rw [map_mul, act'_X, Finset.mul_sum, ← hatL_apply, map_sum]
    simp only [hatL_apply, mul_smul_comm, hat_intCast_smul, hat_mul_X, hp]
    rw [act_mul, act_X, Finset.mul_sum]
    simp only [mul_smul_comm]

/-- The kernel `(z X + Y)^n`. -/
def kernel (n : ℕ) : MvPolynomial (Fin 2) (Polynomial ℂ) :=
  (MvPolynomial.C Polynomial.X * MvPolynomial.X 0 + MvPolynomial.X 1) ^ n

lemma binaryExponent_eq (n j : ℕ) :
    binaryExponent n j = Finsupp.single 0 j + Finsupp.single 1 (n - j) := by
  ext i; fin_cases i <;> simp [binaryExponent]

lemma kernel_eq (n : ℕ) : kernel n = ∑ j ∈ Finset.range (n + 1),
    MvPolynomial.monomial (binaryExponent n j) ((n.choose j : ℂ) • Polynomial.X ^ j) := by
  unfold kernel
  rw [add_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_pow, ← MvPolynomial.C_pow, MvPolynomial.C_mul_X_pow_eq_monomial,
    MvPolynomial.X_pow_eq_monomial, ← MvPolynomial.C_eq_coe_nat, MvPolynomial.C_apply,
    MvPolynomial.monomial_mul_monomial, MvPolynomial.monomial_mul_monomial,
    binaryExponent_eq, add_zero]
  congr 1
  rw [Polynomial.smul_eq_C_mul, mul_one, mul_comm, map_natCast]

/-- `hat` of the kernel is the period polynomial. -/
lemma hat_kernel (Λ : Polynomial ℂ →ₗ[ℂ] ℂ) (n : ℕ) :
    hat Λ (kernel n) = ∑ j ∈ Finset.range (n + 1),
      MvPolynomial.monomial (binaryExponent n j) ((n.choose j : ℂ) * Λ (Polynomial.X ^ j)) := by
  rw [kernel_eq, ← hatL_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hatL_apply, hat_monomial, map_smul, smul_eq_mul]

lemma cuspPeriodPolynomial_eq_hat {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (f : CuspForm (GammaOne N) (k : ℤ)) (r : ℚ) :
    cuspPeriodPolynomial f r = hat (Lam f r (goodAt_of_cuspForm hN hk f r)) (kernel (k - 2)) := by
  rw [hat_kernel, cuspPeriodPolynomial, show k - 2 + 1 = k - 1 by omega]
  rfl

/-- Composition with a polynomial, as a linear map. -/
def compL (q : Polynomial ℂ) : Polynomial ℂ →ₗ[ℂ] Polynomial ℂ where
  toFun P := P.comp q
  map_add' P Q := Polynomial.add_comp
  map_smul' c P := by simp [Polynomial.smul_comp]

@[simp] lemma compL_apply (q P : Polynomial ℂ) : compL q P = P.comp q := rfl

lemma hat_comp (Λ : Polynomial ℂ →ₗ[ℂ] ℂ) (q : Polynomial ℂ) (R) :
    hat (Λ ∘ₗ compL q) R = hat Λ (MvPolynomial.map (Polynomial.compRingHom q) R) := by
  ext m; simp [coeff_hat, MvPolynomial.coeff_map]

lemma map_kernel (q : Polynomial ℂ) (n : ℕ) :
    MvPolynomial.map (Polynomial.compRingHom q) (kernel n) =
      (MvPolynomial.C q * MvPolynomial.X 0 + MvPolynomial.X 1) ^ n := by
  simp [kernel, MvPolynomial.map_C, MvPolynomial.map_X]

lemma act'_X_zero (p q r t : ℤ) :
    act' !![p, q; r, t] (MvPolynomial.X 0) =
      (p : Polynomial ℂ) • MvPolynomial.X 0 + (r : Polynomial ℂ) • MvPolynomial.X 1 := by
  rw [act'_X, Fin.sum_univ_two]
  simp

lemma act'_X_one (p q r t : ℤ) :
    act' !![p, q; r, t] (MvPolynomial.X 1) =
      (q : Polynomial ℂ) • MvPolynomial.X 0 + (t : Polynomial ℂ) • MvPolynomial.X 1 := by
  rw [act'_X, Fin.sum_univ_two]
  simp

lemma act'_kernel_β (l b : ℕ) (n : ℕ) :
    act' (Matrix.adjugate !![1, (b : ℤ); 0, (l : ℤ)]) (kernel n) =
      (MvPolynomial.C (Polynomial.C (l : ℂ) * Polynomial.X - Polynomial.C (b : ℂ)) *
        MvPolynomial.X 0 + MvPolynomial.X 1) ^ n := by
  have hbase : act' (Matrix.adjugate !![1, (b : ℤ); 0, (l : ℤ)])
      (MvPolynomial.C Polynomial.X * MvPolynomial.X 0 + MvPolynomial.X 1) =
      MvPolynomial.C (Polynomial.C (l : ℂ) * Polynomial.X - Polynomial.C (b : ℂ)) *
        MvPolynomial.X 0 + MvPolynomial.X 1 := by
    rw [Matrix.adjugate_fin_two_of, map_add, map_mul, act'_C, act'_X_zero, act'_X_one]
    simp only [MvPolynomial.smul_eq_C_mul, map_sub, map_mul, map_neg, map_natCast,
      Int.cast_natCast, Int.cast_neg, neg_zero, Int.cast_zero, Int.cast_one, map_zero, map_one,
      zero_mul, add_zero, one_mul]
    ring
  unfold kernel
  rw [map_pow, hbase]

lemma act'_kernel_α (l : ℕ) (n : ℕ) :
    act' (Matrix.adjugate !![(l : ℤ), 0; 0, 1]) (kernel n) =
      (MvPolynomial.C Polynomial.X * MvPolynomial.X 0 +
        MvPolynomial.C (Polynomial.C (l : ℂ)) * MvPolynomial.X 1) ^ n := by
  have hbase : act' (Matrix.adjugate !![(l : ℤ), 0; 0, 1])
      (MvPolynomial.C Polynomial.X * MvPolynomial.X 0 + MvPolynomial.X 1) =
      MvPolynomial.C Polynomial.X * MvPolynomial.X 0 +
        MvPolynomial.C (Polynomial.C (l : ℂ)) * MvPolynomial.X 1 := by
    rw [Matrix.adjugate_fin_two_of, map_add, map_mul, act'_C, act'_X_zero, act'_X_one]
    simp only [MvPolynomial.smul_eq_C_mul, map_natCast,
      Int.cast_natCast, neg_zero, Int.cast_zero, Int.cast_one, map_zero, map_one, zero_mul,
      add_zero, one_mul]
    ring
  unfold kernel
  rw [map_pow, hbase]

/-! ### Part C: assembly -/

lemma fractional_β_none (l b : ℕ) : fractional !![1, (b : ℤ); 0, (l : ℤ)] none = none := by
  (simp [fractional]; rfl)

lemma fractional_β_some {l : ℕ} (hl : 0 < l) (b : ℕ) (r : ℚ) :
    fractional !![1, (b : ℤ); 0, (l : ℤ)] (some r) = some ((r + b) / l) := by
  have : (l : ℚ) ≠ 0 := by exact_mod_cast hl.ne'
  (simp [fractional, this]; rfl)

lemma fractional_α_none (l : ℕ) : fractional !![(l : ℤ), 0; 0, 1] none = none := by
  (simp [fractional]; rfl)

lemma fractional_α_some (l : ℕ) (r : ℚ) :
    fractional !![(l : ℤ), 0; 0, 1] (some r) = some (l * r) := by
  (simp [fractional]; rfl)

/-- The vertical-integral functional of `T_l f` in terms of those of `f`. -/
lemma Lam_heckePrime {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (e : ℂ) {l : ℕ} (hl : 0 < l)
    (f g : CuspForm (GammaOne N) (k : ℤ)) (hg : ∀ z, g z = heckePrime k e l f z) (r : ℚ) :
    Lam g r (goodAt_of_cuspForm hN hk g r) =
      ∑ b : Fin l, (Lam f ((r + b.val) / l) (goodAt_of_cuspForm hN hk f _)) ∘ₗ
          compL (Polynomial.C (l : ℂ) * Polynomial.X - Polynomial.C (b.val : ℂ)) +
        (e * (l : ℂ) ^ (k - 1) * (l : ℂ)⁻¹) •
          ((Lam f (l * r) (goodAt_of_cuspForm hN hk f _)) ∘ₗ
            compL (Polynomial.C (l : ℂ)⁻¹ * Polynomial.X)) := by
  apply LinearMap.ext
  intro P
  simp only [Lam_apply, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, compL_apply, smul_eq_mul]
  exact modularIntegral_heckePrime hl k e f g hg r (fun b => goodAt_of_cuspForm hN hk f _)
    (goodAt_of_cuspForm hN hk f _) P

/-- The period polynomial of `T_l f`. -/
lemma cuspPeriodPolynomial_heckePrime {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (e : ℂ) {l : ℕ}
    (hl : 0 < l) (f g : CuspForm (GammaOne N) (k : ℤ)) (hg : ∀ z, g z = heckePrime k e l f z)
    (r : ℚ) :
    cuspPeriodPolynomial g r =
      ∑ b : Fin l, act (Matrix.adjugate !![1, (b.val : ℤ); 0, (l : ℤ)])
          (cuspPeriodPolynomial f ((r + b.val) / l)) +
        e • act (Matrix.adjugate !![(l : ℤ), 0; 0, 1]) (cuspPeriodPolynomial f (l * r)) := by
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  rw [cuspPeriodPolynomial_eq_hat hN hk g r, Lam_heckePrime hN hk e hl f g hg r, hat_add_left,
    hat_sum_left, hat_smul_left]
  congr 1
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [hat_comp, map_kernel, ← act'_kernel_β, hat_act', cuspPeriodPolynomial_eq_hat hN hk f]
  · rw [hat_comp, map_kernel, cuspPeriodPolynomial_eq_hat hN hk f]
    have hkey : (MvPolynomial.C (Polynomial.C (l : ℂ)⁻¹ * Polynomial.X) * MvPolynomial.X 0 +
        MvPolynomial.X 1 : MvPolynomial (Fin 2) (Polynomial ℂ)) ^ (k - 2) =
        MvPolynomial.C (Polynomial.C ((l : ℂ)⁻¹ ^ (k - 2))) *
          act' (Matrix.adjugate !![(l : ℤ), 0; 0, 1]) (kernel (k - 2)) := by
      rw [act'_kernel_α, map_pow, map_pow, ← mul_pow]
      congr 1
      rw [map_mul, mul_add, ← mul_assoc, ← map_mul, ← mul_assoc (MvPolynomial.C _), ← map_mul,
        ← map_mul, inv_mul_cancel₀ hl', map_one, map_one, one_mul, mul_comm (Polynomial.C _)]
    rw [hkey, hat_C_C_mul, hat_act', smul_smul]
    congr 1
    rw [show k - 1 = k - 2 + 1 by omega, pow_succ, inv_pow]
    calc e * ((l : ℂ) ^ (k - 2) * (l : ℂ)) * (l : ℂ)⁻¹ * ((l : ℂ) ^ (k - 2))⁻¹
        = e * ((l : ℂ) * (l : ℂ)⁻¹) * ((l : ℂ) ^ (k - 2) * ((l : ℂ) ^ (k - 2))⁻¹) := by ring
      _ = e := by rw [mul_inv_cancel₀ hl', mul_inv_cancel₀ (pow_ne_zero _ hl')]; ring

/-- **Hecke equivariance of the integration cochain.** -/
theorem integrationCochain_heckePrime {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (e : ℂ) {l : ℕ}
    (hl : 0 < l) (f g : CuspForm (GammaOne N) (k : ℤ)) (hg : ∀ z, g z = heckePrime k e l f z) :
    integrationCochain g = primeHecke e l (integrationCochain f) := by
  have hP : ∀ x : Cusp, cuspPrimitive g x =
      ∑ b : Fin l, act (Matrix.adjugate !![1, (b.val : ℤ); 0, (l : ℤ)])
          (cuspPrimitive f (fractional !![1, (b.val : ℤ); 0, (l : ℤ)] x)) +
        e • act (Matrix.adjugate !![(l : ℤ), 0; 0, 1])
          (cuspPrimitive f (fractional !![(l : ℤ), 0; 0, 1] x)) := by
    intro x
    rcases x with _ | r
    · simp only [fractional_β_none, fractional_α_none]
      simp [cuspPrimitive]
    · simp only [fractional_β_some hl, fractional_α_some]
      exact cuspPeriodPolynomial_heckePrime hN hk e hl f g hg r
  funext D
  simp only [integrationCochain, primeHecke, slash, Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
  rw [hP D.1, hP D.2]
  simp only [map_sub, Finset.sum_sub_distrib, smul_sub]
  abel

end MTT.HeckeEquiv

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ)
    (hI : ∀ f, (I f).val = integrationCochain f) :
    HeckeEquivariant I := by
  intro e l hl f g hg
  rw [hI g, hI f]
  exact MTT.HeckeEquiv.integrationCochain_heckePrime hN hk (e l) hl.pos f g hg
end

end privateSection

public section publicSection

noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology
theorem MTT.Cohomology.integration_cochain_hecke_equivariant
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ)
    (hI : ∀ f, (I f).val = integrationCochain f) :
    HeckeEquivariant I := _root_.solution hN hk I hI
end

end publicSection
