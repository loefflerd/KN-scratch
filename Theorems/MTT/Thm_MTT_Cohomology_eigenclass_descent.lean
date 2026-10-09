/-
Based on Prove2Me node MTT.Cohomology.eigenclass_descent
(6a58ed1c-e5cb-41f8-b00c-78f187d4cf0b) by davidloeffler (2026-09-06).

Proof based on Prove2Me submission 0a41a358-c633-4ca1-9c9c-cd108c830b65
by allychan327 (2026-09-06); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import Definitions.MTT.Def_MTT_Cohomology
public import Mathlib.RingTheory.Flat.Basic

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit

/-!
# Descent of a signed eigenline to algebraic coefficients

Theorem statement: `MTT.Cohomology.eigenclass_descent` (`6a58ed1c-e5cb-41f8-b00c-78f187d4cf0b`), by
davidloeffler, 2026-09-06.

Proof: submission `0a41a358-c633-4ca1-9c9c-cd108c830b65`, by allychan327, 2026-09-06 (ACCEPTED);
locally adapted.

Given integral finite generation, the two canonical base-change isomorphisms, and dimension at most
one for a signed algebraic Hecke eigenpacket, every complex class in that packet is a nonzero
complex scalar times a coefficientwise algebraic class. The zero class is allowed and may use scalar
1. This is finite-dimensional linear algebra applied to the explicitly defined algebraic Hecke,
nebentype and sign equations; it assumes no period theorem.

## Explanation of the source proof

## Setup

Write $M_R = \mathrm{Hc}(N,n,R)$ and let $K = \iota(\overline{\mathbf Q}) \subset \mathbf C$.
Let $V_{\mathbf C} \subset M_{\mathbf C}$ be the set of classes satisfying the eigenpacket
equations `Packet` for the character $\iota\circ\varepsilon$, the eigenvalues
$\iota\circ a$ and the sign $s$. The hypothesis `hdim` says $\dim_{\mathbf C} V_{\mathbf C}\le 1$.

Given $0 \ne \phi \in V_{\mathbf C}$, it therefore suffices to produce **one nonzero
element of $V_{\mathbf C}$ that is defined over $\overline{\mathbf Q}$**: if $x = \psi^{\iota}$
is such an element, then $\phi = c\,x$ with $c \ne 0$, and $\omega = c$ works. The zero class
is handled separately with $\omega = 1$, $\psi = 0$.

## The three inputs, and what each is used for

**Base change over $\mathbf C$** writes $\phi$ over the integral lattice. Every element of
$\mathbf C \otimes_{\mathbf Z} M_{\mathbf Z}$ is a *finite* sum of pure tensors, so
$$\phi = \sum_{i \in T} c_i\, G_i, \qquad c_i \in \mathbf C,\ \ G_i = e_{\mathbf C}(1\otimes g_i),$$
and the pure-tensor clause says each $G_i$ extends the integral class $g_i$ coefficientwise.

**Base change over $\overline{\mathbf Q}$** supplies $\hat G_i = e_{\overline{\mathbf Q}}(1\otimes
g_i)$.
Since $\iota \circ (\mathbf Z \to \overline{\mathbf Q}) = (\mathbf Z \to \mathbf C)$ — there is only
one ring map out of $\mathbf Z$ — we get $\mathrm{Extends}\ \iota\ \hat G_i\ G_i$. So the
spanning family $\{G_i\}$ of $\phi$ consists of *algebraic* classes: this is the predicate
`Alg` in the Lean file, "$v$ is the coefficientwise $\iota$-image of a
$\overline{\mathbf Q}$-valued datum".

$\mathrm{hZ}$ is not needed: finiteness of $T$ already comes from the tensor product.

## Descent

Regard $\mathbf C$ as a $\overline{\mathbf Q}$-vector space through $\iota$, choose a basis
$(b_t)$, and let $\pi_t : \mathbf C \to \overline{\mathbf Q}$ be the coordinate functionals;
they are additive and satisfy $\pi_t(\iota(q)z) = q\,\pi_t(z)$. Put
$$\Phi_t = \sum_{i\in T} \iota(\pi_t(c_i))\, G_i \in M_{\mathbf C},
\qquad \Psi_t = \sum_{i\in T} \pi_t(c_i)\, \hat G_i \in M_{\overline{\mathbf Q}} .$$
By construction $\mathrm{Extends}\ \iota\ \Psi_t\ \Phi_t$, so each $\Phi_t$ is algebraic.

*Each $\Phi_t$ still lies in $V_{\mathbf C}$.* Every `Packet` equation has the shape
$D(\phi) = 0$ for a $\mathbf C$-linear operator $D$ built from `act` by integral matrices,
`fractional`/`cuspAct` reparametrisations of the cusps, and multiplication by
$\iota(\varepsilon(l))$, $\iota(a_l)$, $\mathrm{sign}(s)$. Two facts drive the argument:

1. $D$ is $\mathbf C$-linear in the class (`primeHecke_lin`, `reflection_lin`,
   `precomp_lin`, `actAt_lin`, `smul_lin`), so $\sum_i c_i\, w_i = 0$ where
   $w_i := D(G_i)$;
2. each $w_i$ is again algebraic. This is the lemma `act_map`: `act A` is the substitution
   $P(X,Y) \mapsto P((X,Y)A)$ with $A$ integral, hence commutes with any coefficient ring
   map, and $\iota(q)\cdot \mathrm{map}\,\iota\,P = \mathrm{map}\,\iota\,(q\cdot P)$.

So in each monomial coefficient the relation reads $\sum_i c_i\,\iota(q_i) = 0$ with
$q_i \in \overline{\mathbf Q}$. Applying $\pi_t$ gives $\sum_i q_i\,\pi_t(c_i) = 0$, and
applying $\iota$ again gives $\sum_i \iota(\pi_t(c_i))\,\iota(q_i) = 0$, i.e.
$\sum_i \iota(\pi_t(c_i))\, w_i = 0$, which is exactly $D(\Phi_t) = 0$. This is the lemma
`descent`, applied once for each of the three clauses of `Packet`.

*Some $\Phi_t$ is nonzero.* Expanding $c_i = \sum_t \iota(\pi_t(c_i))\, b_t$ over a finite
common index set and exchanging the two sums gives $\phi = \sum_t b_t\, \Phi_t$; so
$\phi \ne 0$ forces $\Phi_{t} \ne 0$ for some $t$.

## Conclusion

$\Phi_t$ and $\phi$ are two nonzero members of $V_{\mathbf C}$, so `hdim` gives
$u\,\Phi_t + v\,\phi = 0$ with $u,v$ not both zero; neither can vanish (else the other
class would), so $\phi = \omega\,\Phi_t$ with $\omega = -u/v \ne 0$ and
$\omega^{-1}\phi = \Phi_t$, which extends $\Psi_t$.

<!-- Generated by add_prove2me_provenance.py -->
-/

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology


namespace P2MDesc

open MvPolynomial

/-! ### Coefficientwise extension commutes with the integral operators -/

/-- The substitution operator attached to an integral matrix is defined over `ℤ`,
hence commutes with any coefficient ring map. -/
theorem act_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A : Matrix (Fin 2) (Fin 2) ℤ) (P : Binary R) :
    act A (MvPolynomial.map f P) = MvPolynomial.map f (act A P) := by
  unfold act
  simp only [AlgHom.toLinearMap_apply]
  show MvPolynomial.bind₁ (fun i : Fin 2 => ∑ a : Fin 2, (A a i : S) • MvPolynomial.X a)
      (MvPolynomial.map f P)
    = MvPolynomial.map f (MvPolynomial.bind₁
        (fun i : Fin 2 => ∑ a : Fin 2, (A a i : R) • MvPolynomial.X a) P)
  have hfun : (fun i : Fin 2 =>
      MvPolynomial.map f (∑ a : Fin 2, (A a i : R) • MvPolynomial.X a))
      = fun i : Fin 2 => (∑ a : Fin 2, (A a i : S) • MvPolynomial.X a) := by
    funext i
    simp [MvPolynomial.smul_eq_C_mul]
  rw [MvPolynomial.map_bind₁, hfun]

theorem map_smul_eq {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a : R) (P : Binary R) :
    MvPolynomial.map f (a • P) = f a • MvPolynomial.map f P := by
  simp [MvPolynomial.smul_eq_C_mul]

end P2MDesc

namespace P2MDesc

open MvPolynomial

/-! ### Algebraic modular-symbol data -/

/-- A `ℂ`-valued datum on divisors is *algebraic* (relative to `ι`) when it is the
coefficientwise image of a `Qbar`-valued datum. -/
def Alg (ι : MTT.Qbar →+* ℂ) (v : (Cusp × Cusp) → Binary ℂ) : Prop :=
  ∃ u : (Cusp × Cusp) → Binary MTT.Qbar, ∀ D, v D = MvPolynomial.map ι (u D)

variable {ι : MTT.Qbar →+* ℂ}

theorem Alg.coeff {v : (Cusp × Cusp) → Binary ℂ} (h : Alg ι v) (D : Cusp × Cusp)
    (d : Fin 2 →₀ ℕ) : AddMonoidAlgebra.coeff (v D) d ∈ Set.range ι := by
  obtain ⟨u, hu⟩ := h
  exact ⟨AddMonoidAlgebra.coeff (u D) d, by rw [hu D, MvPolynomial.coeff_map]⟩

theorem Alg.zero : Alg ι 0 := ⟨0, by simp⟩

theorem Alg.add {v w : (Cusp × Cusp) → Binary ℂ} (hv : Alg ι v) (hw : Alg ι w) :
    Alg ι (v + w) := by
  obtain ⟨u, hu⟩ := hv; obtain ⟨t, ht⟩ := hw
  exact ⟨u + t, by intro D; simp [hu D, ht D]⟩

theorem Alg.neg {v : (Cusp × Cusp) → Binary ℂ} (hv : Alg ι v) : Alg ι (-v) := by
  obtain ⟨u, hu⟩ := hv
  exact ⟨-u, by intro D; simp [hu D]⟩

theorem Alg.sub {v w : (Cusp × Cusp) → Binary ℂ} (hv : Alg ι v) (hw : Alg ι w) :
    Alg ι (v - w) := by
  simpa [sub_eq_add_neg] using hv.add hw.neg

theorem Alg.smul {v : (Cusp × Cusp) → Binary ℂ} (a : MTT.Qbar) (hv : Alg ι v) :
    Alg ι ((ι a) • v) := by
  obtain ⟨u, hu⟩ := hv
  refine ⟨a • u, fun D => ?_⟩
  simp only [Pi.smul_apply, hu D]
  rw [map_smul_eq ι a (u D)]

theorem Alg.sum {α : Type*} (S : Finset α) (v : α → ((Cusp × Cusp) → Binary ℂ))
    (h : ∀ i ∈ S, Alg ι (v i)) : Alg ι (∑ i ∈ S, v i) := by
  classical
  induction S using Finset.induction with
  | empty => simpa using (Alg.zero (ι := ι))
  | insert i S hi ih =>
      rw [Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self _ _)).add
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem Alg.precomp {v : (Cusp × Cusp) → Binary ℂ} (hv : Alg ι v)
    (σ : Cusp × Cusp → Cusp × Cusp) : Alg ι (fun D => v (σ D)) := by
  obtain ⟨u, hu⟩ := hv
  exact ⟨fun D => u (σ D), fun D => hu (σ D)⟩

theorem Alg.actAt {v : (Cusp × Cusp) → Binary ℂ} (hv : Alg ι v)
    (A : Matrix (Fin 2) (Fin 2) ℤ) : Alg ι (fun D => act A (v D)) := by
  obtain ⟨u, hu⟩ := hv
  refine ⟨fun D => act A (u D), fun D => ?_⟩
  dsimp only
  rw [hu D, act_map ι A (u D)]

theorem Alg.slash {v : (Cusp × Cusp) → Binary ℂ} (hv : Alg ι v)
    (g : Matrix (Fin 2) (Fin 2) ℤ) : Alg ι (MTT.Cohomology.slash g v) := by
  exact (hv.precomp fun D => (fractional g D.1, fractional g D.2)).actAt (Matrix.adjugate g)

theorem Alg.reflection {v : (Cusp × Cusp) → Binary ℂ} (hv : Alg ι v) :
    Alg ι (MTT.Cohomology.reflection v) := by
  exact (hv.precomp fun D => (fractional !![-1, 0; 0, 1] D.1,
      fractional !![-1, 0; 0, 1] D.2)).actAt !![-1, 0; 0, 1]

theorem Alg.primeHecke {v : (Cusp × Cusp) → Binary ℂ} (hv : Alg ι v)
    (a : MTT.Qbar) (l : ℕ) : Alg ι (MTT.Cohomology.primeHecke (ι a) l v) := by
  refine Alg.add ?_ (Alg.smul a (Alg.slash hv _))
  have h := Alg.sum (ι := ι) (Finset.univ : Finset (Fin l))
    (fun b => MTT.Cohomology.slash !![1, (b.val : ℤ); 0, (l : ℤ)] v)
    (fun b _ => Alg.slash hv _)
  exact h

end P2MDesc

namespace P2MDesc

open MvPolynomial

/-! ### Linearity of the integral operators in the class -/

variable {α : Type*}

theorem smul_lin (b : ℂ) (S : Finset α) (c : α → ℂ)
    (v : α → ((Cusp × Cusp) → Binary ℂ)) :
    b • (∑ i ∈ S, c i • v i) = ∑ i ∈ S, c i • (b • v i) := by
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_comm b (c i) (v i)

theorem precomp_lin (σ : Cusp × Cusp → Cusp × Cusp) (S : Finset α) (c : α → ℂ)
    (v : α → ((Cusp × Cusp) → Binary ℂ)) :
    (fun D => (∑ i ∈ S, c i • v i) (σ D)) = ∑ i ∈ S, c i • (fun D => v i (σ D)) := by
  funext D
  simp [Finset.sum_apply]

theorem actAt_lin (A : Matrix (Fin 2) (Fin 2) ℤ) (S : Finset α) (c : α → ℂ)
    (v : α → ((Cusp × Cusp) → Binary ℂ)) :
    (fun D => act A ((∑ i ∈ S, c i • v i) D))
      = ∑ i ∈ S, c i • (fun D => act A (v i D)) := by
  funext D
  simp [Finset.sum_apply, map_sum]

theorem slash_lin (g : Matrix (Fin 2) (Fin 2) ℤ) (S : Finset α) (c : α → ℂ)
    (v : α → ((Cusp × Cusp) → Binary ℂ)) :
    MTT.Cohomology.slash g (∑ i ∈ S, c i • v i)
      = ∑ i ∈ S, c i • MTT.Cohomology.slash g (v i) := by
  funext D
  simp [MTT.Cohomology.slash, Finset.sum_apply, map_sum]

theorem primeHecke_lin (b : ℂ) (l : ℕ) (S : Finset α) (c : α → ℂ)
    (v : α → ((Cusp × Cusp) → Binary ℂ)) :
    MTT.Cohomology.primeHecke b l (∑ i ∈ S, c i • v i)
      = ∑ i ∈ S, c i • MTT.Cohomology.primeHecke b l (v i) := by
  simp only [MTT.Cohomology.primeHecke, slash_lin, smul_lin]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_add, Finset.smul_sum]

theorem reflection_lin (S : Finset α) (c : α → ℂ)
    (v : α → ((Cusp × Cusp) → Binary ℂ)) :
    MTT.Cohomology.reflection (∑ i ∈ S, c i • v i)
      = ∑ i ∈ S, c i • MTT.Cohomology.reflection (v i) := by
  funext D
  simp [MTT.Cohomology.reflection, Finset.sum_apply, map_sum]

/-! ### The descent step -/

variable {ι : MTT.Qbar →+* ℂ}

/-- A `ℂ`-linear relation among algebraic data survives applying a `Qbar`-semilinear
functional to its coefficients. -/
theorem descent (S : Finset α) (c : α → ℂ)
    (w : α → ((Cusp × Cusp) → Binary ℂ))
    (halg : ∀ i ∈ S, Alg ι (w i))
    (h0 : ∑ i ∈ S, c i • w i = 0)
    (π : ℂ →+ MTT.Qbar)
    (hsm : ∀ (q : MTT.Qbar) (z : ℂ), π (ι q * z) = q * π z) :
    ∑ i ∈ S, (ι (π (c i))) • w i = 0 := by
  classical
  funext D
  ext d
  have hq : ∀ i : α, ∃ q : MTT.Qbar,
      i ∈ S → AddMonoidAlgebra.coeff (w i D) d = ι q := by
    intro i
    by_cases hi : i ∈ S
    · obtain ⟨y, hy⟩ := (halg i hi).coeff D d
      exact ⟨y, fun _ => hy.symm⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose q hq using hq
  have h0' : ∑ i ∈ S, c i * ι (q i) = 0 := by
    have := congrArg (fun F => AddMonoidAlgebra.coeff (F D) d) h0
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply,
      MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul,
      AddMonoidAlgebra.coeff_zero] at this
    change (∑ i ∈ S, c i * AddMonoidAlgebra.coeff (w i D) d) = 0 at this
    rw [← this]
    exact Finset.sum_congr rfl fun i hi => by rw [hq i hi]
  have hπ : ∑ i ∈ S, q i * π (c i) = 0 := by
    have := congrArg π h0'
    rw [map_sum, map_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_comm (c i), hsm]
  have hι : ∑ i ∈ S, ι (q i) * ι (π (c i)) = 0 := by
    have := congrArg ι hπ
    rw [map_sum, map_zero] at this
    simpa using this
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply,
    MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul,
    AddMonoidAlgebra.coeff_zero]
  change (∑ i ∈ S, ι (π (c i)) * AddMonoidAlgebra.coeff (w i D) d) = 0
  rw [← hι]
  exact Finset.sum_congr rfl fun i hi => by rw [hq i hi, mul_comm]

end P2MDesc

open scoped BigOperators TensorProduct
open MTT.Cohomology

set_option linter.unusedVariables false in
open P2MDesc MvPolynomial in
theorem solution {N n : ℕ} (hZ : Module.Finite ℤ (Hc N n ℤ))
    (hQ : BaseChange N n MTT.Qbar) (hC : BaseChange N n ℂ)
    (ι : MTT.Qbar →+* ℂ) (e : DirichletCharacter MTT.Qbar N)
    (a : ℕ → MTT.Qbar) (s : Bool)
    (hdim : ∀ φ ψ : Hc N n ℂ,
      Packet (fun d => ι (e d)) (fun l => ι (a l)) s φ →
      Packet (fun d => ι (e d)) (fun l => ι (a l)) s ψ →
      ∃ u v : ℂ, (u ≠ 0 ∨ v ≠ 0) ∧ u • φ + v • ψ = 0)
    (φ : Hc N n ℂ)
    (hφ : Packet (fun d => ι (e d)) (fun l => ι (a l)) s φ) :
    ∃ ω : ℂ, ω ≠ 0 ∧ ∃ ψ : Hc N n MTT.Qbar, Extends ι ψ (ω⁻¹ • φ) := by
  classical
  obtain ⟨eC, hCe⟩ := hC
  obtain ⟨eQ, hQe⟩ := hQ
  obtain ⟨T, hT⟩ := TensorProduct.exists_finset (eC.symm φ)
  set G : ℂ × Hc N n ℤ → Hc N n ℂ := fun i => eC (1 ⊗ₜ[ℤ] i.2) with hGdef
  set Gq : ℂ × Hc N n ℤ → Hc N n MTT.Qbar := fun i => eQ (1 ⊗ₜ[ℤ] i.2) with hGqdef
  ------------------------------------------------------------------
  -- 1.  `φ` is a finite ℂ-combination of coefficientwise-integral classes.
  ------------------------------------------------------------------
  have hdecomp : φ = ∑ i ∈ T, i.1 • G i := by
    conv_lhs => rw [← eC.apply_symm_apply φ, hT]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← LinearEquiv.map_smul eC]
    congr 1
    rw [TensorProduct.smul_tmul']
    simp
  have hval : φ.val = ∑ i ∈ T, i.1 • (G i).val := by rw [hdecomp]; push_cast; rfl
  ------------------------------------------------------------------
  -- 2.  Those classes are algebraic: they are ι-images of Qbar-classes.
  ------------------------------------------------------------------
  have hExt : ∀ i, ∀ D : Cusp × Cusp, (G i).val D = MvPolynomial.map ι ((Gq i).val D) := by
    intro i D
    have h1 := hCe i.2 D.1 D.2
    have h2 := hQe i.2 D.1 D.2
    rw [h2, MvPolynomial.map_map]
    have hcomp : ι.comp (Int.castRingHom MTT.Qbar) = Int.castRingHom ℂ := RingHom.ext_int _ _
    rw [hcomp]
    exact h1
  have halgG : ∀ i, Alg ι ((G i).val) := fun i => ⟨(Gq i).val, hExt i⟩
  ------------------------------------------------------------------
  -- 3.  A Qbar-coordinate system on ℂ.
  ------------------------------------------------------------------
  let : Module MTT.Qbar ℂ := ι.toModule
  set B := Module.Basis.ofVectorSpace MTT.Qbar ℂ with hB
  set π : ↥(Module.Basis.ofVectorSpaceIndex MTT.Qbar ℂ) → (ℂ →+ MTT.Qbar) :=
    fun t => (B.coord t).toAddMonoidHom with hπ
  have hsm : ∀ t (q : MTT.Qbar) (z : ℂ), π t (ι q * z) = q * π t z := by
    intro t q z
    have hz : ι q * z = q • z := rfl
    simp only [hπ, LinearMap.toAddMonoidHom_coe, hz, map_smul, smul_eq_mul]
  have h1 : ∀ z : ℂ, ∑ t ∈ (B.repr z).support, ι (π t z) * (B t : ℂ) = z := by
    intro z
    have h := B.linearCombination_repr z
    rw [Finsupp.linearCombination_apply, Finsupp.sum] at h
    calc ∑ t ∈ (B.repr z).support, ι (π t z) * (B t : ℂ)
        = ∑ t ∈ (B.repr z).support, (B.repr z t) • (B t : ℂ) :=
          Finset.sum_congr rfl fun t _ => rfl
      _ = z := h
  ------------------------------------------------------------------
  -- 4.  The descended candidates.
  ------------------------------------------------------------------
  set Φ : ↥(Module.Basis.ofVectorSpaceIndex MTT.Qbar ℂ) → Hc N n ℂ :=
    fun t => ∑ i ∈ T, (ι (π t i.1)) • G i with hΦ
  set Ψ : ↥(Module.Basis.ofVectorSpaceIndex MTT.Qbar ℂ) → Hc N n MTT.Qbar :=
    fun t => ∑ i ∈ T, (π t i.1) • Gq i with hΨ
  have hvalΦ : ∀ t, (Φ t).val = ∑ i ∈ T, (ι (π t i.1)) • (G i).val := by
    intro t; rw [hΦ]; push_cast; rfl
  have hExtΦ : ∀ t, Extends ι (Ψ t) (Φ t) := by
    intro t x y
    have hb : (Ψ t).val = ∑ i ∈ T, (π t i.1) • (Gq i).val := by rw [hΨ]; push_cast; rfl
    rw [hvalΦ t, hb]
    simp only [Finset.sum_apply, Pi.smul_apply]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul_eq ι, ← hExt i (x, y)]
  ------------------------------------------------------------------
  -- 5.  Each candidate satisfies the same eigenpacket equations.
  ------------------------------------------------------------------
  have hsign : ((MTT.sign s : ℤ) : ℂ) = ι (((MTT.sign s : ℤ) : MTT.Qbar)) := by
    rw [map_intCast]
  have hPacket : ∀ t, Packet (fun d => ι (e d)) (fun l => ι (a l)) s (Φ t) := by
    intro t
    refine ⟨?_, ?_, ?_⟩
    · -- prime Hecke eigenvalue
      intro l hl
      set w : ℂ × Hc N n ℤ → ((Cusp × Cusp) → Binary ℂ) :=
        fun i => MTT.Cohomology.primeHecke (ι (e l)) l ((G i).val)
          - (ι (a l)) • (G i).val with hw
      have halgw : ∀ i ∈ T, Alg ι (w i) := fun i _ =>
        Alg.sub ((halgG i).primeHecke (e l) l) (Alg.smul (a l) (halgG i))
      have hw0 : ∑ i ∈ T, i.1 • w i = 0 := by
        have e1 := primeHecke_lin (ι (e l)) l T (fun i => i.1) (fun i => (G i).val)
        have e2 := smul_lin (ι (a l)) T (fun i => i.1) (fun i => (G i).val)
        simp only [hw, smul_sub, Finset.sum_sub_distrib]
        rw [← e1, ← e2, ← hval, hφ.1 l hl, sub_self]
      have hd := descent T (fun i => i.1) w halgw hw0 (π t) (hsm t)
      simp only [hw, smul_sub, Finset.sum_sub_distrib, sub_eq_zero] at hd
      rw [hvalΦ t, primeHecke_lin, smul_lin]
      exact hd
    · -- nebentype
      intro γ x y
      set σ : Cusp × Cusp → Cusp × Cusp :=
        fun D => (cuspAct γ.val D.1, cuspAct γ.val D.2) with hσ
      set A : Matrix (Fin 2) (Fin 2) ℤ := γ.val.val with hA
      set κ : MTT.Qbar := e ((γ.val 1 1 : ℤ) : ZMod N) with hκ
      set w : ℂ × Hc N n ℤ → ((Cusp × Cusp) → Binary ℂ) :=
        fun i => (fun D => (G i).val (σ D)) - (ι κ) • (fun D => act A ((G i).val D)) with hw
      have halgw : ∀ i ∈ T, Alg ι (w i) := fun i _ =>
        Alg.sub ((halgG i).precomp σ) (Alg.smul κ ((halgG i).actAt A))
      have hw0 : ∑ i ∈ T, i.1 • w i = 0 := by
        have e1 := precomp_lin σ T (fun i => i.1) (fun i => (G i).val)
        have e2 := actAt_lin A T (fun i => i.1) (fun i => (G i).val)
        have e3 := smul_lin (ι κ) T (fun i => i.1) (fun i => (fun D => act A ((G i).val D)))
        simp only [hw, smul_sub, Finset.sum_sub_distrib]
        rw [← e1, ← e3, ← e2, ← hval]
        have hpt : (fun D : Cusp × Cusp => φ.val (σ D))
            = (ι κ) • (fun D : Cusp × Cusp => act A (φ.val D)) := by
          funext D
          simpa [hσ, hA, hκ] using hφ.2.1 γ D.1 D.2
        rw [hpt, sub_self]
      have hd := descent T (fun i => i.1) w halgw hw0 (π t) (hsm t)
      simp only [hw, smul_sub, Finset.sum_sub_distrib, sub_eq_zero] at hd
      have hgoal : (fun D : Cusp × Cusp => (Φ t).val (σ D))
          = (ι κ) • (fun D : Cusp × Cusp => act A ((Φ t).val D)) := by
        rw [hvalΦ t, precomp_lin, actAt_lin, smul_lin]
        exact hd
      simpa [hσ, hA, hκ] using congrFun hgoal (x, y)
    · -- reflection sign
      set w : ℂ × Hc N n ℤ → ((Cusp × Cusp) → Binary ℂ) :=
        fun i => MTT.Cohomology.reflection ((G i).val)
          - ((MTT.sign s : ℤ) : ℂ) • (G i).val with hw
      have halgw : ∀ i ∈ T, Alg ι (w i) := by
        intro i _
        refine Alg.sub (halgG i).reflection ?_
        rw [hsign]
        exact Alg.smul _ (halgG i)
      have hw0 : ∑ i ∈ T, i.1 • w i = 0 := by
        have e1 := reflection_lin T (fun i => i.1) (fun i => (G i).val)
        have e2 := smul_lin (((MTT.sign s : ℤ) : ℂ)) T (fun i => i.1) (fun i => (G i).val)
        simp only [hw, smul_sub, Finset.sum_sub_distrib]
        rw [← e1, ← e2, ← hval, hφ.2.2, sub_self]
      have hd := descent T (fun i => i.1) w halgw hw0 (π t) (hsm t)
      simp only [hw, smul_sub, Finset.sum_sub_distrib, sub_eq_zero] at hd
      rw [hvalΦ t, reflection_lin, smul_lin]
      exact hd
  ------------------------------------------------------------------
  -- 6.  The candidates span `φ`, so one of them is nonzero.
  ------------------------------------------------------------------
  set Tset : Finset ↥(Module.Basis.ofVectorSpaceIndex MTT.Qbar ℂ) :=
    T.biUnion (fun i => (B.repr i.1).support) with hTset
  have hcoord : ∀ i ∈ T, ∑ t ∈ Tset, ι (π t i.1) * (B t : ℂ) = i.1 := by
    intro i hi
    have hsub : (B.repr i.1).support ⊆ Tset := fun t ht =>
      Finset.mem_biUnion.mpr ⟨i, hi, ht⟩
    have hzs : ∀ t ∈ Tset, t ∉ (B.repr i.1).support → ι (π t i.1) * (B t : ℂ) = 0 := by
      intro t _ hts
      have hzero : B.repr i.1 t = 0 := by simpa using hts
      have hq : π t i.1 = 0 := hzero
      rw [hq, map_zero, zero_mul]
    rw [← Finset.sum_subset hsub hzs]
    exact h1 i.1
  have hphi_sum : φ = ∑ t ∈ Tset, (B t : ℂ) • Φ t := by
    rw [hdecomp]
    have hstep : ∀ i ∈ T, i.1 • G i = ∑ t ∈ Tset, (ι (π t i.1) * (B t : ℂ)) • G i := by
      intro i hi
      rw [← Finset.sum_smul, hcoord i hi]
    rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hΦ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_comm]
  ------------------------------------------------------------------
  -- 7.  Conclusion.
  ------------------------------------------------------------------
  by_cases hφ0 : φ = 0
  · refine ⟨1, one_ne_zero, 0, ?_⟩
    intro x y
    simp [hφ0]
  · have hex : ∃ t ∈ Tset, Φ t ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hφ0
      rw [hphi_sum]
      refine Finset.sum_eq_zero fun t ht => ?_
      rw [hcon t ht, smul_zero]
    obtain ⟨t, _, ht0⟩ := hex
    obtain ⟨u, v, huv, hrel⟩ := hdim (Φ t) φ (hPacket t) hφ
    have hv : v ≠ 0 := by
      rintro rfl
      rw [zero_smul, add_zero] at hrel
      rcases huv with hu | hv
      · exact ht0 ((smul_eq_zero.mp hrel).resolve_left hu)
      · exact hv rfl
    have hu : u ≠ 0 := by
      rintro rfl
      rw [zero_smul, zero_add] at hrel
      exact hφ0 ((smul_eq_zero.mp hrel).resolve_left hv)
    have hω : φ = (v⁻¹ * (-u)) • Φ t := by
      have hh : v • φ = (-u) • Φ t := by
        have h2 : u • Φ t + v • φ - u • Φ t = 0 - u • Φ t := by rw [hrel]
        simp only [add_sub_cancel_left, zero_sub] at h2
        rw [h2]
        exact (neg_smul u (Φ t)).symm
      calc φ = v⁻¹ • (v • φ) := by rw [smul_smul, inv_mul_cancel₀ hv, one_smul]
        _ = v⁻¹ • ((-u) • Φ t) := by rw [hh]
        _ = (v⁻¹ * (-u)) • Φ t := by rw [smul_smul]
    refine ⟨v⁻¹ * (-u), by simp [hv, hu], Ψ t, ?_⟩
    have : (v⁻¹ * (-u))⁻¹ • φ = Φ t := by
      rw [hω, smul_smul, inv_mul_cancel₀ (by simp [hv, hu]), one_smul]
    rw [this]
    exact hExtΦ t
end

end privateSection

public section publicSection

noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.eigenclass_descent
    {N n : ℕ} (hZ : Module.Finite ℤ (Hc N n ℤ))
    (hQ : BaseChange N n MTT.Qbar) (hC : BaseChange N n ℂ)
    (ι : MTT.Qbar →+* ℂ) (e : DirichletCharacter MTT.Qbar N)
    (a : ℕ → MTT.Qbar) (s : Bool)
    (hdim : ∀ φ ψ : Hc N n ℂ,
      Packet (fun d => ι (e d)) (fun l => ι (a l)) s φ →
      Packet (fun d => ι (e d)) (fun l => ι (a l)) s ψ →
      ∃ u v : ℂ, (u ≠ 0 ∨ v ≠ 0) ∧ u • φ + v • ψ = 0)
    (φ : Hc N n ℂ)
    (hφ : Packet (fun d => ι (e d)) (fun l => ι (a l)) s φ) :
    ∃ ω : ℂ, ω ≠ 0 ∧ ∃ ψ : Hc N n MTT.Qbar, Extends ι ψ (ω⁻¹ • φ) := _root_.solution hZ hQ hC ι e a s hdim φ hφ
end

end publicSection
