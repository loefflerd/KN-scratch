/-
Based on Prove2Me node MTT.Cohomology.packet_span
(42324074-503b-4041-82f9-841078a389a1) by cbirkbeck (2026-09-06).

Proof based on Prove2Me submission a89845da-b3d7-4e98-9f93-3e5adf1c2dde
by cbirkbeck (2026-09-07); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import Definitions.MTT.Def_MTT_Cohomology

import Definitions.MTT.Def_MTT_Cohomology_Boundary
import Theorems.MTT.Thm_MTT_Cohomology_eichler_shimura_span
import Theorems.MTT.Thm_MTT_Cohomology_eichler_shimura_nebentype_compatible
import Theorems.MTT.Thm_MTT_Cohomology_eichler_shimura_hecke_compatible_char
import Theorems.MTT.Thm_MTT_Cohomology_image_packet_unique
import Theorems.MTT.Thm_MTT_Cohomology_boundary_packet_zero
import Theorems.MTT.Thm_MTT_Cohomology_reflection_class
import Theorems.MTT.Thm_MTT_Cohomology_reflection_involutive

/-!
# The full-packet eigenspace in $H^1_c$ is spanned by $I(f)$ and its reflection

Theorem statement: `MTT.Cohomology.packet_span` (`42324074-503b-4041-82f9-841078a389a1`), by
cbirkbeck, 2026-09-06.

Proof: submission `a89845da-b3d7-4e98-9f93-3e5adf1c2dde`, by cbirkbeck, 2026-09-07 (ACCEPTED);
locally adapted.

Let $N>0$, $k\ge 2$, and let $H_c=H_c(N,k-2;\mathbf
C)=\operatorname{Hom}_{\Gamma_1(N)}(\operatorname{Div}^0(\mathbf P^1(\mathbf
Q)),\operatorname{Sym}^{k-2}\mathbf C^2)$ be the space of $\operatorname{Sym}^{k-2}$-valued modular
symbols of level $\Gamma_1(N)$ (the compactly supported cohomology of the mission). Let
$I:S_k(\Gamma_1(N))\to H_c$ be the cusp-to-cusp integration map, characterised by its coefficient
evaluations (`IntegralClass`) and Hecke-equivariant for the explicit prime Hecke operators
(`HeckeEquivariant`), and let $\mathcal R$ be the reflection induced by $\operatorname{diag}(-1,1)$.

Let $f$ be a normalised cuspidal eigenform of weight $k$ on $\Gamma_1(N)$ with nebentypus
$\varepsilon$ and eigenvalues $a_\ell$ at **every** prime $\ell$ (the operator at a prime dividing
$N$ is $U_\ell$, since $\varepsilon(\ell)=0$ there). Suppose $\phi\in H_c$ satisfies the same
eigen-equations as $f$:

$$
T_\ell\,\phi=a_\ell\,\phi\quad\text{for every prime }\ell,\qquad
\phi(\gamma x,\gamma y)=\varepsilon(d_\gamma)\,\gamma\cdot\phi(x,y)\quad\text{for every
}\gamma\in\Gamma_0(N).
$$

Then $\phi$ lies in the complex span of the class of $f$ and its reflection:

$$
\phi \;=\; c\, I(f) + d\,\mathcal R\big(I(f)\big)\qquad\text{for some } c,d\in\mathbf C .
$$

This is the cohomological multiplicity-one statement behind the Eichler–Shimura isomorphism: the
eigenspace of the full prime eigenpacket and nebentypus of a cuspidal eigenform inside $H^1_c$ is
spanned by the holomorphic class $I(f)$ and the antiholomorphic class $\mathcal R(I(f))$. It
combines three classical inputs: Eichler–Shimura ($H_c$ is the direct sum of the holomorphic
classes, the antiholomorphic classes and the boundary symbols, compatibly with the Hecke and
nebentype operators), multiplicity one for the full packet in $S_k(\Gamma_1(N))$ (including the
$U_\ell$ at primes dividing the level, for arbitrary eigenforms, old or new), and the exclusion of a
cuspidal eigenpacket from the boundary summand. No sign condition is imposed; the signed statement
follows by linear algebra.

**Formalization Note** The integration map is a hypothesis of the theorem: any linear map $I$ with
`IntegralClass` and `HeckeEquivariant` (it is unique by `MTT.Cohomology.integral_class_unique`). The
two hypotheses on $\phi$ are the first two conjuncts of `Packet`; the reflection $\mathcal R$ is
`reflection` applied to the underlying cochain.

## Explanation of the source proof

# The full-packet eigenspace from the Eichler–Shimura decomposition

We reduce

$$
\phi\in H_c(N,k-2;\mathbf C),\ \ T_\ell\phi=a_\ell\phi\ (\forall\ell),\ \ \phi\ \text{has
nebentypus}\ \varepsilon
\ \Longrightarrow\ \phi=c\,I(f)+d\,\mathcal R\big(I(f)\big)
$$

to five classical statements about modular symbols and two facts about the reflection $\mathcal R$.
The children are assumptions of this submission.

## The children

1. `eichler_shimura_span`: $\phi=I(g)+\mathcal R(I(h))+\partial\Phi$ with $g,h$ cusp forms and
   $\Phi$ a boundary datum.
2. `eichler_shimura_nebentype_compatible`: if the sum satisfies the nebentype law for $e$, so does
   each summand.
3. `eichler_shimura_hecke_compatible`: for summands obeying the nebentype law for $e$, if the sum is
   a $T_\ell$-eigenvector with eigenvalue $a$, so is each summand ($T_\ell$ taken with the scalar
   $e(\ell)$, hence $U_\ell$ at primes dividing $N$).
4. `image_packet_unique`: a cusp form whose class carries the nebentype law of $f$ and all its prime
   eigenvalues is a multiple of $f$.
5. `boundary_packet_zero`: a boundary cochain carrying that packet is zero.
6. `reflection_class` (proved): $\mathcal R$ preserves $H_c$, commutes with every prime Hecke
   operator, and preserves the nebentype law.
7. `reflection_involutive` (proved): $\mathcal R\circ\mathcal R=\mathrm{id}$.

## The reduction

Decompose $\phi=I(g)+\mathcal R(I(h))+\partial\Phi$ by (1). The nebentype law for $\phi$ passes to
the three summands by (2); then, for each prime $\ell$, the eigen-equation $T_\ell\phi=a_\ell\phi$
passes to the three summands by (3).

**Holomorphic summand.** $I(g)$ carries the full packet, so $g=c\,f$ by (4) and $I(g)=c\,I(f)$ by
linearity.

**Reflected summand.** $\mathcal R(I(h))$ carries the packet. Applying $\mathcal R$ and using (6)
and (7): the nebentype law for $\mathcal R(I(h))$ transfers to $\mathcal R\mathcal R(I(h))=I(h)$,
and from $T_\ell\mathcal R(I(h))=a_\ell\mathcal R(I(h))$ we get
$$
T_\ell I(h)=\mathcal R\mathcal R\,T_\ell I(h)=\mathcal R\,T_\ell\,\mathcal R I(h)=\mathcal
R\big(a_\ell\,\mathcal R I(h)\big)=a_\ell\,I(h).
$$
So $I(h)$ carries the packet, $h=d\,f$ by (4), and $\mathcal R(I(h))=d\,\mathcal R(I(f))$.

**Boundary summand.** $\partial\Phi$ carries the packet, hence vanishes by (5).

Therefore $\phi=c\,I(f)+d\,\mathcal R(I(f))$.

<!-- Generated by add_prove2me_provenance.py -->
-/

section privateSection

noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

namespace P2MPS

theorem reflection_smul {R : Type*} [CommRing R] (a : R) (φ : (Cusp × Cusp) → Binary R) :
    reflection (a • φ) = a • reflection φ := by
  funext D; simp [reflection]

end P2MPS

open P2MPS in
theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ)
    (hI : ∀ f, IntegralClass f (I f)) (hT : HeckeEquivariant I)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) (φ : Hc N (k-2) ℂ)
    (hφH : ∀ l : ℕ, l.Prime →
      primeHecke (ι (f.epsilon (l : ZMod N))) l φ.val = ι (f.coeff l) • φ.val)
    (hφε : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      φ.val (cuspAct γ.val x, cuspAct γ.val y) =
        ι (f.epsilon (γ.val 1 1 : ZMod N)) • act γ.val.val (φ.val (x, y))) :
    ∃ c d : ℂ, φ.val = c • (I f.form).val + d • reflection (I f.form).val := by
  set e : ZMod N → ℂ := fun d => ι (f.epsilon d) with he
  obtain ⟨g, h, Φ, hΦ, hdec⟩ := MTT.Cohomology.eichler_shimura_span hN hk I hI φ
  -- the nebentype law passes to the three summands
  have hlaw : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      ((I g).val + reflection (I h).val + boundaryCochain Φ) (cuspAct γ.val x, cuspAct γ.val y) =
        e (γ.val 1 1 : ZMod N) •
          act γ.val.val (((I g).val + reflection (I h).val + boundaryCochain Φ) (x, y)) := by
    intro γ x y; rw [← hdec]; exact hφε γ x y
  obtain ⟨hg, hh, hb⟩ :=
    MTT.Cohomology.eichler_shimura_nebentype_compatible hN hk I hI g h Φ hΦ e hlaw
  -- the Hecke equations pass to the three summands
  have hH : ∀ l : ℕ, l.Prime →
      primeHecke (e (l : ZMod N)) l (I g).val = ι (f.coeff l) • (I g).val ∧
      primeHecke (e (l : ZMod N)) l (reflection (I h).val) = ι (f.coeff l) • reflection (I h).val ∧
      primeHecke (e (l : ZMod N)) l (boundaryCochain Φ) = ι (f.coeff l) • boundaryCochain Φ := by
    intro l hl
    refine MTT.Cohomology.eichler_shimura_hecke_compatible_char hN hk I hI hT g h Φ hΦ
      (f.epsilon.ringHomComp ι) hg hh hb
      l hl (ι (f.coeff l)) ?_
    rw [← hdec]; exact hφH l hl
  -- the holomorphic summand
  obtain ⟨c, hc⟩ := MTT.Cohomology.image_packet_unique hN hk I hI hT ι f g hg
    (fun l hl => (hH l hl).1)
  -- the antiholomorphic summand: pull the equations back through the involution
  have hh' : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      (I h).val (cuspAct γ.val x, cuspAct γ.val y) =
        e (γ.val 1 1 : ZMod N) • act γ.val.val ((I h).val (x, y)) := by
    obtain ⟨ψ, hψ⟩ := (MTT.Cohomology.reflection_class (I h)).1
    have := (MTT.Cohomology.reflection_class ψ).2.2 e (by rw [hψ]; exact hh)
    rw [hψ, MTT.Cohomology.reflection_involutive] at this
    exact this
  have hH' : ∀ l : ℕ, l.Prime →
      primeHecke (e (l : ZMod N)) l (I h).val = ι (f.coeff l) • (I h).val := by
    intro l hl
    have h1 := (hH l hl).2.1
    have hcomm := (MTT.Cohomology.reflection_class (I h)).2.1 (e (l : ZMod N)) l
    -- reflection (primeHecke (I h)) = primeHecke (reflection (I h)) = a • reflection (I h)
    have h2 : reflection (primeHecke (e (l : ZMod N)) l (I h).val) =
        reflection (ι (f.coeff l) • (I h).val) := by
      rw [hcomm, h1, reflection_smul]
    have h3 := congrArg reflection h2
    simpa [MTT.Cohomology.reflection_involutive] using h3
  obtain ⟨d, hd⟩ := MTT.Cohomology.image_packet_unique hN hk I hI hT ι f h hh' hH'
  -- the boundary summand vanishes
  have hb0 : boundaryCochain Φ = 0 :=
    MTT.Cohomology.boundary_packet_zero hN hk ι f Φ hΦ hb (fun l hl => (hH l hl).2.2)
  refine ⟨c, d, ?_⟩
  rw [hdec, hb0, hc, hd, map_smul, map_smul, add_zero]
  simp [reflection_smul]
end

end privateSection

public section publicSection

noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.packet_span
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ)
    (hI : ∀ f, IntegralClass f (I f)) (hT : HeckeEquivariant I)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) (φ : Hc N (k-2) ℂ)
    (hφH : ∀ l : ℕ, l.Prime →
      primeHecke (ι (f.epsilon (l : ZMod N))) l φ.val = ι (f.coeff l) • φ.val)
    (hφε : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      φ.val (cuspAct γ.val x, cuspAct γ.val y) =
        ι (f.epsilon (γ.val 1 1 : ZMod N)) • act γ.val.val (φ.val (x, y))) :
    ∃ c d : ℂ, φ.val = c • (I f.form).val + d • reflection (I f.form).val := _root_.solution hN hk I hI hT ι f φ hφH hφε
end

end publicSection
