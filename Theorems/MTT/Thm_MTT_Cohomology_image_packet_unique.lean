/-
Based on Prove2Me node MTT.Cohomology.image_packet_unique
(45a3d1fa-a4ff-4041-8d81-1301a7b99c56) by cbirkbeck (2026-09-06).

Proof based on Prove2Me submission 2b23c98d-9338-43e4-addb-449103450701
by cbirkbeck (2026-09-06); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import Definitions.MTT.Def_MTT_Cohomology_Boundary

import Theorems.MTT.Thm_MTT_Cohomology_character_law_of_class
import Theorems.MTT.Thm_MTT_exists_cuspForm_heckePrime_pos
import Theorems.MTT.Thm_MTT_hasSum_heckePrime
import Theorems.MTT.Thm_MTT_coeff_eq_of_hecke_recurrence
import Theorems.MTT.Thm_MTT_period_vanishing

/-!
# Multiplicity one for the full prime eigenpacket: a class with the packet of $f$ comes from $\mathbf C\,f$

Theorem statement: `MTT.Cohomology.image_packet_unique` (`45a3d1fa-a4ff-4041-8d81-1301a7b99c56`), by
cbirkbeck, 2026-09-06.

Proof: submission `2b23c98d-9338-43e4-addb-449103450701`, by cbirkbeck, 2026-09-06 (ACCEPTED);
locally adapted.

Let $f$ be a normalised cuspidal eigenform of weight $k\ge2$ on $\Gamma_1(N)$ with nebentypus
$\varepsilon$ and eigenvalues $a_\ell$ at every prime ($U_\ell$ at $\ell\mid N$). Let $g\in
S_k(\Gamma_1(N))$ be a cusp form whose modular symbol $I(g)$ satisfies the nebentype law for
$\varepsilon$ and the eigen-equations

$$
T_\ell\,I(g)=a_\ell\,I(g)\qquad\text{for every prime }\ell .
$$

Then $g=c\,f$ for some $c\in\mathbf C$.

This is multiplicity one for the **full** packet, oldforms and $p$-stabilisations included, and it
does not need the Atkin–Lehner–Li structure theory. Transferring the equations to $g$ (the
integration map is injective and Hecke-equivariant), the Hecke equations on Fourier coefficients
read $b_{\ell m}=a_\ell b_m-\varepsilon(\ell)\ell^{k-1}b_{m/\ell}$ for $\ell\nmid N$ and $b_{\ell
m}=a_\ell b_m$ for $\ell\mid N$, which determine every coefficient from $b_1$ by strong induction;
since $f$ satisfies the same recurrences with first coefficient $1$, $g=b_1f$.

**Formalization Note** The hypotheses are placed on the class $I(g)$, as produced by the
Eichler–Shimura decomposition; the transfer to $g$ uses `IntegralClass`, `HeckeEquivariant`, and the
vanishing theorem `MTT.period_vanishing`.

## Explanation of the source proof

We reduce multiplicity one for the image of the integration map to four lemmas, which are
assumptions of this submission, together with the sibling problem `MTT.period_vanishing`.

**Setting.** $I:S_k(\Gamma_1(N))\to H_c$ is linear, has the integral-class property and is
Hecke-equivariant in the mission's sense; $f$ is the normalised eigenform with nebentypus
$\varepsilon$ and eigenvalues $a_\ell=\iota(\text{coeff}_\ell)$; $g\in S_k(\Gamma_1(N))$ is a cusp
form whose class $I(g)$ satisfies the nebentype law for $\iota\circ\varepsilon$ and the Hecke
equations $T_\ell\,I(g)=a_\ell\,I(g)$ at every prime $\ell$. We must show $g=c\,f$ for some
$c\in\mathbf C$.

**Step 0: $q$-expansions.** The cusp $\infty$ of $\Gamma_1(N)$ has width one
(`CongruenceSubgroup.strictPeriods_Gamma1`), so every cusp form $h$ on $\Gamma_1(N)$ satisfies
$h(\tau)=\sum_{n\ge0}a_n(h)\,q_\tau^{\,n}$ at every $\tau$ (`ModularForm.hasSum_qExpansion`), its
constant term vanishes (`CuspFormClass.qExpansion_coeff_zero`), and any coefficient sequence
representing $h$ this way is its $q$-expansion (`ModularFormClass.qExpansion_coeff_unique`). For $f$
the coefficients are $\iota(\text{coeff}_n)$ by the structure field `coeff_eq`.

**Step 1: injectivity of $I$.** If $I(h)=0$ then the integral-class property gives
$\binom{k-2}{j}\cdot(\text{modular integral of }h\text{ against }X^j\text{ at }r)=0$ for all $j\le
k-2$ and $r\in\mathbf Q$; the binomial coefficient is non-zero, so all modular integrals of $h$
vanish and `MTT.period_vanishing` gives $h=0$. Hence $I$ is injective
(`injective_of_integralClass`).

**Step 2: the law descends to $g$.** By the child lemma `MTT.Cohomology.character_law_of_class`, the
nebentype law on the class $I(g)$ implies $g(\gamma z)=\iota(\varepsilon(d))(cz+d)^kg(z)$ for
$\gamma\in\Gamma_0(N)$: $g$ has nebentypus $\iota\circ\varepsilon$, which we view as the Dirichlet
character $e=\varepsilon^{\iota}$ (`MulChar.ringHomComp`).

**Step 3: Hecke eigen-equations for $g$.** Fix a prime $\ell$. By the child lemma
`MTT.exists_cuspForm_heckePrime`, $T_\ell g$ (the mission's pointwise operator with the scalar
$e(\ell)$) is a cusp form $g_\ell$ on $\Gamma_1(N)$. Hecke-equivariance of $I$ gives
$I(g_\ell)=T_\ell\,I(g)$ on the level of cochains, and the hypothesis on $I(g)$ turns this into
$I(g_\ell)=a_\ell\,I(g)=I(a_\ell g)$. Injectivity yields $g_\ell=a_\ell\,g$, i.e. $T_\ell
g=a_\ell\,g$ pointwise.

**Step 4: the coefficient recurrences.** By the child lemma `MTT.hasSum_heckePrime`, $T_\ell g$ has
the convergent expansion $\sum_n\big(a_{\ell n}(g)+e(\ell)\ell^{k-1}[\ell\mid
n]a_{n/\ell}(g)\big)q^n$ at every point; by Step 3 the same function $a_\ell g$ also has the
expansion $\sum_na_\ell a_n(g)q^n$. Uniqueness of $q$-expansions (applied to the cusp form $a_\ell
g$) gives, for every prime $\ell$ and $m\ge0$,
$$a_{\ell m}(g)+e(\ell)\,\ell^{k-1}[\ell\mid m]\,a_{m/\ell}(g)=a_\ell\,a_m(g).$$
Exactly the same argument with the structure field `eigen` in place of Step 3 gives the same
recurrences for the coefficients $\iota(\text{coeff}_m)$ of $f$.

**Step 5: conclusion.** Both coefficient sequences satisfy the prime Hecke recurrences with the same
data, and $f$ is normalised, so the child lemma `MTT.coeff_eq_of_hecke_recurrence` gives
$a_m(g)=a_1(g)\,\iota(\text{coeff}_m)$ for all $m\ge1$; for $m=0$ both sides vanish (constant terms
of cusp forms). Therefore $g$ and $a_1(g)\,f$ have the same $q$-expansion at every $\tau$, and
uniqueness of limits (`HasSum.unique`) gives $g=a_1(g)\,f$ pointwise, hence as cusp forms
(`CuspForm.ext`). Thus $c=a_1(g)$.

This is the Fourier-coefficient proof of multiplicity one for the full prime eigenpacket
(Diamond–Shurman §5.8; Williams, Theorem 9.10), run inside $H_c$ through the injective,
Hecke-equivariant integration map. No non-vanishing of $L$-values is used.

<!-- Generated by add_prove2me_provenance.py -->
-/

section privateSection

noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

namespace MTT.Cohomology

/-- `1` is a strict period of `Γ₁(N)` viewed inside `GL₂(ℝ)`. -/
theorem one_mem_strictPeriods_gammaOne (N : ℕ) :
    (1 : ℝ) ∈ (MTT.GammaOne N).strictPeriods := by
  rw [show MTT.GammaOne N = (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
    CongruenceSubgroup.strictPeriods_Gamma1]
  exact ⟨1, by simp⟩

/-- Any integration map is injective: this is `period_vanishing` read through `IntegralClass`. -/
theorem injective_of_integralClass {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ)
    (hI : ∀ f, IntegralClass f (I f)) : Function.Injective I := by
  intro f g hfg
  have h0 : I (f - g) = 0 := by rw [map_sub, hfg, sub_self]
  have hcls := hI (f - g)
  rw [h0] at hcls
  have hzero : f - g = 0 := MTT.period_vanishing hN hk (f - g) (fun j hj r => by
    have h := hcls j r hj
    rw [map_zero] at h
    have hch : (((k-2).choose j : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj).ne'
    exact (mul_eq_zero.mp h.symm).resolve_left hch)
  exact sub_eq_zero.mp hzero

end MTT.Cohomology

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ)
    (hI : ∀ f, IntegralClass f (I f)) (hT : HeckeEquivariant I)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) (g : CuspForm (MTT.GammaOne N) (k : ℤ))
    (hlaw : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      (I g).val (cuspAct γ.val x, cuspAct γ.val y) =
        ι (f.epsilon (γ.val 1 1 : ZMod N)) • act γ.val.val ((I g).val (x, y)))
    (hH : ∀ l : ℕ, l.Prime →
      primeHecke (ι (f.epsilon (l : ZMod N))) l (I g).val = ι (f.coeff l) • (I g).val) :
    ∃ c : ℂ, g = c • f.form := by
  -- q-expansions at the cusp ∞ of Γ₁(N), which has width one
  have h1 : (1 : ℝ) ∈ (MTT.GammaOne N).strictPeriods := one_mem_strictPeriods_gammaOne N
  have : Fact (IsCusp OnePoint.infty (MTT.GammaOne N)) :=
    ⟨(MTT.GammaOne N).isCusp_of_mem_strictPeriods one_pos h1⟩
  have hfa : ∀ σ : UpperHalfPlane,
      HasSum (fun n ↦ ι (f.coeff n) • Function.Periodic.qParam (1 : ℝ) (σ : ℂ) ^ n)
        (f.form σ) := by
    intro σ
    have := ModularForm.hasSum_qExpansion f.form one_pos h1 σ
    simpa [f.coeff_eq, smul_eq_mul] using this
  have hgb : ∀ σ : UpperHalfPlane,
      HasSum (fun n ↦ (UpperHalfPlane.qExpansion 1 g).coeff n •
        Function.Periodic.qParam (1 : ℝ) (σ : ℂ) ^ n) (g σ) := by
    intro σ
    have := ModularForm.hasSum_qExpansion g one_pos h1 σ
    simpa [smul_eq_mul] using this
  -- the nebentype law for `g` itself
  have hglaw := character_law_of_class hN hk I hI (fun d => ι (f.epsilon d)) g hlaw
  let e : DirichletCharacter ℂ N := f.epsilon.ringHomComp ι
  have he : ∀ d : ZMod N, e d = ι (f.epsilon d) := fun d => rfl
  have hinj := injective_of_integralClass hN hk I hI
  -- the Hecke eigen-equations for `g`, transported through `I`
  have hgeig : ∀ l : ℕ, l.Prime → ∀ z : UpperHalfPlane,
      MTT.heckePrime k (ι (f.epsilon l)) l g z = ι (f.coeff l) * g z := by
    intro l hl
    obtain ⟨gl, hgl, -⟩ := MTT.exists_cuspForm_heckePrime_pos hN (by omega) e g
      (fun γ z => by rw [he]; exact hglaw γ z) l hl
    have hIgl : (I gl).val = primeHecke (e l) l (I g).val := hT e l hl g gl hgl
    have hEq : I gl = I (ι (f.coeff l) • g) := by
      apply Subtype.ext
      rw [hIgl, he, hH l hl, map_smul]
      rfl
    have hgl' := hinj hEq
    intro z
    rw [← he, ← hgl, hgl']
    simp
  -- the coefficient recurrences, by comparing q-expansions
  have hrec_b : ∀ p : ℕ, p.Prime → ∀ m : ℕ,
      (UpperHalfPlane.qExpansion 1 g).coeff (p * m) +
        ι (f.epsilon p) * (p : ℂ) ^ (k - 1) *
          (if p ∣ m then (UpperHalfPlane.qExpansion 1 g).coeff (m / p) else 0) =
        ι (f.coeff p) * (UpperHalfPlane.qExpansion 1 g).coeff m := by
    intro p hp m
    have hs1 : ∀ τ : UpperHalfPlane, HasSum (fun n ↦
        ((UpperHalfPlane.qExpansion 1 g).coeff (p * n) + ι (f.epsilon p) * (p : ℂ) ^ (k - 1) *
          (if p ∣ n then (UpperHalfPlane.qExpansion 1 g).coeff (n / p) else 0)) •
          Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ n) ((ι (f.coeff p) • g) τ) := by
      intro τ
      have := MTT.hasSum_heckePrime k (ι (f.epsilon p)) hp (g : UpperHalfPlane → ℂ)
        (fun n ↦ (UpperHalfPlane.qExpansion 1 g).coeff n) τ hgb
      rw [hgeig p hp τ] at this
      simpa [smul_eq_mul] using this
    have hs2 : ∀ τ : UpperHalfPlane, HasSum (fun n ↦
        (ι (f.coeff p) * (UpperHalfPlane.qExpansion 1 g).coeff n) •
          Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ n) ((ι (f.coeff p) • g) τ) := by
      intro τ
      have := (hgb τ).const_smul (ι (f.coeff p))
      simpa [smul_eq_mul, mul_assoc] using this
    have u1 := ModularFormClass.qExpansion_coeff_unique one_pos h1 (f := ι (f.coeff p) • g) hs1 m
    have u2 := ModularFormClass.qExpansion_coeff_unique one_pos h1 (f := ι (f.coeff p) • g) hs2 m
    exact u1.trans u2.symm
  have hrec_a : ∀ p : ℕ, p.Prime → ∀ m : ℕ,
      ι (f.coeff (p * m)) + ι (f.epsilon p) * (p : ℂ) ^ (k - 1) *
          (if p ∣ m then ι (f.coeff (m / p)) else 0) =
        ι (f.coeff p) * ι (f.coeff m) := by
    intro p hp m
    have hs1 : ∀ τ : UpperHalfPlane, HasSum (fun n ↦
        (ι (f.coeff (p * n)) + ι (f.epsilon p) * (p : ℂ) ^ (k - 1) *
          (if p ∣ n then ι (f.coeff (n / p)) else 0)) •
          Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ n) ((ι (f.coeff p) • f.form) τ) := by
      intro τ
      have := MTT.hasSum_heckePrime k (ι (f.epsilon p)) hp (f.form : UpperHalfPlane → ℂ)
        (fun n ↦ ι (f.coeff n)) τ hfa
      rw [f.eigen p hp τ] at this
      simpa [smul_eq_mul] using this
    have hs2 : ∀ τ : UpperHalfPlane, HasSum (fun n ↦
        (ι (f.coeff p) * ι (f.coeff n)) •
          Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ n) ((ι (f.coeff p) • f.form) τ) := by
      intro τ
      have := (hfa τ).const_smul (ι (f.coeff p))
      simpa [smul_eq_mul, mul_assoc] using this
    have u1 := ModularFormClass.qExpansion_coeff_unique one_pos h1 (f := ι (f.coeff p) • f.form) hs1 m
    have u2 := ModularFormClass.qExpansion_coeff_unique one_pos h1 (f := ι (f.coeff p) • f.form) hs2 m
    exact u1.trans u2.symm
  -- constant terms vanish
  have hb0 : (UpperHalfPlane.qExpansion 1 g).coeff 0 = 0 :=
    CuspFormClass.qExpansion_coeff_zero g one_pos h1
  have ha0 : ι (f.coeff 0) = 0 := by
    rw [← f.coeff_eq 0]
    exact CuspFormClass.qExpansion_coeff_zero f.form one_pos h1
  -- the recurrence determines the coefficients from the first one
  have hP2 := MTT.coeff_eq_of_hecke_recurrence k (fun p => ι (f.epsilon p)) (fun p => ι (f.coeff p))
    (fun n => (UpperHalfPlane.qExpansion 1 g).coeff n) (fun n => ι (f.coeff n)) hrec_b hrec_a
    (by simp [f.normalized])
  refine ⟨(UpperHalfPlane.qExpansion 1 g).coeff 1, ?_⟩
  ext τ
  have h2 : HasSum (fun n ↦ (UpperHalfPlane.qExpansion 1 g).coeff n •
      Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ n)
      ((UpperHalfPlane.qExpansion 1 g).coeff 1 • f.form τ) := by
    have := (hfa τ).const_smul ((UpperHalfPlane.qExpansion 1 g).coeff 1)
    convert this using 1
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hb0, ha0]
    · rw [hP2 n hn, smul_smul]
  exact (hgb τ).unique h2
end

end privateSection

public section publicSection

noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.image_packet_unique
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ)
    (hI : ∀ f, IntegralClass f (I f)) (hT : HeckeEquivariant I)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) (g : CuspForm (MTT.GammaOne N) (k : ℤ))
    (hlaw : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      (I g).val (cuspAct γ.val x, cuspAct γ.val y) =
        ι (f.epsilon (γ.val 1 1 : ZMod N)) • act γ.val.val ((I g).val (x, y)))
    (hH : ∀ l : ℕ, l.Prime →
      primeHecke (ι (f.epsilon (l : ZMod N))) l (I g).val = ι (f.coeff l) • (I g).val) :
    ∃ c : ℂ, g = c • f.form := _root_.solution hN hk I hI hT ι f g hlaw hH
end

end publicSection
