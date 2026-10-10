/-
Based on Prove2Me node HorizontalPadicL.eigenform_residualGaloisRepresentation_exists_v2
(813fe5d1-f931-4a2c-afc7-ad2fac39d094) by davidloeffler (2026-09-20).

Proof based on Prove2Me submission 76b25940-22dd-4d01-a25a-8a961f4b72d2
by riccardo.brasca (2026-09-23); locally adapted.

Licensed under Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
-/

module

public import Definitions.KN.Def_KN_EigenformResidualGaloisRepresentationV2

import Theorems.KN.Thm_MTT_Eigenform_exists_adic_matrix_representation
import Theorems.FLT.Thm_NumberField_exists_lift_mem_inertia_integralClosure
import Theorems.FLT.Thm_ValuationSubring_exists_liesOverPrime_mem_inertiaSubgroupIn
import Definitions.FLT.Def_TaylorWiles_Primes
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Theorems.FLT.Thm_NumberField_exists_isFrobenius_lift_arithFrobAt
import Theorems.FLT.Thm_NumberField_exists_valuationSubring_eq_localization
import Theorems.FLT.Thm_ValuationSubring_isFrobeniusAt_of_forall_smul_sub_pow_mem

/-!
# The residual Galois representation of a normalized eigenform

Theorem statement: `HorizontalPadicL.eigenform_residualGaloisRepresentation_exists_v2`
(`813fe5d1-f931-4a2c-afc7-ad2fac39d094`), by davidloeffler, 2026-09-20.

Proof: submission `76b25940-22dd-4d01-a25a-8a961f4b72d2`, by riccardo.brasca, 2026-09-23
(SKETCH_ACCEPTED); locally adapted.

**This is a formalization of a standard textbook result, so should be low-priority**

Let $N>0$, let $k\geq2$, let $p$ be prime, and let $f$ be a normalized
algebraic cuspidal Hecke eigenform of level $N$, weight $k$, and nebentype
$\varepsilon_f$. For every embedding
$\iota_p:\overline{\mathbf Q}\hookrightarrow\mathbf C_p$, there exists a
finite Galois extension $L/\mathbf Q$ and a faithful residual representation
$$
\bar\rho_{f,\iota_p}:\operatorname{Gal}(L/\mathbf Q)
\longrightarrow M_2(k_{f,\iota_p})
$$
over the canonical finite coefficient residue field. It is unramified outside
$Np$, and for every prime $\ell\nmid Np$ its arithmetic Frobenius satisfies
$$
\operatorname{tr}\bar\rho_{f,\iota_p}(\operatorname{Frob}_\ell)
=\overline{a_\ell(f)},\qquad
\det\bar\rho_{f,\iota_p}(\operatorname{Frob}_\ell)
=\overline{\varepsilon_f(\ell)\ell^{k-1}}.
$$

The representation is written on the finite Galois group of its kernel field,
which is equivalent to the usual finite-image representation of the absolute
Galois group.

## Explanation of the source proof

For a normalized algebraic cuspidal eigenform of level $N>0$ and weight $k\ge2$, fix the embedding
into $\mathbb C_p$, and write

$$K=K_f,\qquad P=\mathfrak p_{f,\iota_p},\qquad
\kappa=\mathcal O_K/P.$$

This submission reduces the exact residual-representation statement to **one open child**,
`MTT.Eigenform.exists_adic_matrix_representation`: Deligne's representation on a stable integral
lattice over the canonical completion. That characteristic-zero existence theorem is assumed by this
sketch, not proved here. The reduction to $\kappa$, the faithful finite Galois kernel field,
unramifiedness, and both required arithmetic Frobenius formulas are proved in the submission using
existing proved platform lemmas.

The child is the integral form of Deligne–Serre, *Formes modulaires de poids 1*, Theorem 6.1, p.520,
together with the stable-lattice construction in §6.12, p.523. Despite the paper's title, Theorem
6.1 explicitly covers weight at least two and arbitrary nebentype; it does not require newness. It
may be applied over the exact coefficient field $K$. The child supplies a representation

$$\rho:G_{\mathbb Q}\longrightarrow
\mathrm{GL}_2\!\left(\widehat{\mathcal O}_{K,P}\right),\qquad
\widehat{\mathcal O}_{K,P}=\varprojlim_n\mathcal O_K/P^n,$$

with finite-level factorization modulo every ideal power, trivial inertia outside $Np$, and the
characteristic-zero arithmetic Frobenius trace and determinant. These are genuinely integral data;
neither a residual representation nor its kernel field is assumed.

**Reduction over the prescribed residue field.** The canonical map

$$r:\widehat{\mathcal O}_{K,P}\longrightarrow\mathcal O_K/P$$

is `AdicCompletion.evalOneₐ`. Its composite with the inclusion of $\mathcal O_K$ is exactly the
target's ideal quotient map. Apply $r$ entrywise to $\rho$. The resulting representation is over the
specific type `EigenformResidueField f ιp`, with no enlargement or replacement of that field.
Finite-level factorization follows from the child's congruence statement at exponent one. Ring
homomorphisms commute with trace and determinant, so reduction gives

$$\operatorname{tr}\bar\rho(\operatorname{Frob}_\ell)
=\overline{a_\ell(f)},\qquad
\det\bar\rho(\operatorname{Frob}_\ell)
=\overline{\varepsilon_f(\ell)\ell^{k-1}}.$$

It also preserves the identity on inertia.

**The faithful kernel field.** A representation factoring through a finite level has open kernel:
its kernel contains the open fixing subgroup of a finite intermediate extension. Since the absolute
Galois group is profinite, this kernel is also closed. Its fixed field

$$L=\overline{\mathbb Q}^{\ker\bar\rho}$$

is finite over $\mathbb Q$ and Galois, because the kernel is normal. Infinite Galois correspondence
identifies its Galois group with the quotient by the kernel. The induced homomorphism into matrices
is injective. The proof works for an arbitrary monoid target by first passing to the group of units,
so the target's matrix-monoid formulation introduces no invertibility assumption.

**Unramifiedness at finite primes.** Fix a prime $\ell\nmid Np$ and an ideal $Q\subset\mathcal O_L$
above $\ell$. Every element of its inertia subgroup lifts to an absolute automorphism acting
trivially on the residue field of an integral-closure prime. Existing proved lifting lemmas realize
this automorphism in the inertia subgroup of a valuation above $\ell$. The absolute representation
kills it. Compatibility with restriction and faithfulness of the descended representation force the
original finite inertia element to be the identity. Thus the actual ideal inertia group required by
the target is trivial.

**The chosen arithmetic Frobenius.** Existing proved lemmas lift the target's particular
`arithFrobAt` at $Q$ to an absolute automorphism and a valuation for which the residue action is
$x\mapsto x^\ell$. The absolute Frobenius formulas therefore apply to this lift. The descended
representation agrees with the absolute one after restriction, yielding the target's trace and
determinant equations for every prime $Q$ above $\ell$.

The top-level `theorem solution` has exactly the original binders and conclusion. All its code is
free of proof placeholders. Its sole open theorem dependency is the integral Deligne existence
child; all other imported theorem nodes are already Proved. Completion, coefficient prime, and
coefficient residue field are concrete constructions, and the finite kernel field is built by Galois
correspondence.

Sources: [Deligne–Serre (1974), §6](https://publications.ias.edu/sites/default/files/Number24.pdf),
Theorem 6.1 and §6.12; their arithmetic Frobenius convention is specified on p.513. The integral
representation and reduction used by the mission appear in [Kriz–Nordentoft, §4, equation
(4.2)](https://arxiv.org/html/2310.20678v3#S4).

<!-- Generated by add_prove2me_provenance.py -->
-/

section privateSection

-- From Solutions/ResidualMatrixReduction.lean
noncomputable section BundleResidualMatrixReduction

open NumberField

lemma GaloisFactorsThroughFiniteLevel.comp
    {M M' : Type} [MulOneClass M] [MulOneClass M']
    {ρ : (MTT.Qbar ≃ₐ[ℚ] MTT.Qbar) →* M}
    (hρ : GaloisFactorsThroughFiniteLevel ρ) (φ : M →* M') :
    GaloisFactorsThroughFiniteLevel (φ.comp ρ) := by
  obtain ⟨L, hL, hfix⟩ := hρ
  exact ⟨L, hL, fun σ hσ ↦ by simp [hfix σ hσ]⟩

namespace MTT.Eigenform

theorem exists_residual_matrix_representation
    {N k p : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (ιp : MTT.Qbar →+* ℂ_[p]) :
    ∃ ρ : (MTT.Qbar ≃ₐ[ℚ] MTT.Qbar) →*
        Matrix (Fin 2) (Fin 2) (f.coefficientResidueField ιp),
      GaloisFactorsThroughFiniteLevel ρ ∧
      (∀ (l : ℕ), l.Prime → Nat.Coprime l (N * p) →
        ∀ A : ValuationSubring MTT.Qbar, A.LiesOverPrime l →
          ∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
      (∀ (l : ℕ), l.Prime → Nat.Coprime l (N * p) →
        ∀ A : ValuationSubring MTT.Qbar, A.LiesOverPrime l →
          ∀ σ : MTT.Qbar ≃ₐ[ℚ] MTT.Qbar, A.IsFrobeniusAt σ l →
            Matrix.trace (ρ σ) = Ideal.Quotient.mk (f.coefficientPrime ιp)
                (f.integralCoeff hN hk l) ∧
            Matrix.det (ρ σ) = Ideal.Quotient.mk (f.coefficientPrime ιp)
                (f.integralNebentype (l : ZMod N) *
                  (l : 𝓞 f.coefficientField) ^ (k - 1))) := by
  obtain ⟨ρ, hfinite, hunram, hfrob⟩ :=
    f.exists_adic_matrix_representation hN hk ι ιp
  let red := f.coefficientReduction ιp
  let ρbar := (red.mapMatrix (m := Fin 2)).toMonoidHom.comp ρ
  refine ⟨ρbar, ?_, ?_, ?_⟩
  · let φ : (𝓞 f.coefficientField) ⧸ f.coefficientPrime ιp ^ 1 →+*
        f.coefficientResidueField ιp := Ideal.Quotient.factor (by simp)
    exact (hfinite 1).comp (φ.mapMatrix (m := Fin 2)).toMonoidHom
  · intro l hl hlNp A hA σ hσ
    change red.mapMatrix (m := Fin 2) (ρ σ) = 1
    rw [hunram l hl hlNp A hA σ hσ, map_one]
  · intro l hl hlNp A hA σ hσ
    obtain ⟨htr, hdet⟩ := hfrob l hl hlNp A hA σ hσ
    constructor
    · change Matrix.trace ((ρ σ).map red) = _
      rw [← AddMonoidHom.map_trace, htr]
      exact f.coefficientReduction_algebraMap ιp _
    · change Matrix.det (red.mapMatrix (ρ σ)) = _
      rw [← RingHom.map_det, hdet]
      exact f.coefficientReduction_algebraMap ιp _

end MTT.Eigenform

end BundleResidualMatrixReduction

noncomputable section BundleResidualFiniteDescent

namespace HorizontalPadicL

private local instance : IsGalois ℚ (AlgebraicClosure ℚ) :=
  @IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) _ _

/-- An open-kernel homomorphism of the absolute Galois group has a faithful
realization on the Galois group of a finite Galois number field. -/
theorem exists_faithful_finiteGalois_descent
    {G : Type*} [Group G]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* G)
    (hker : IsOpen (ρ.ker : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))) :
    ∃ (F : IntermediateField ℚ (AlgebraicClosure ℚ))
      (_ : NumberField F) (_ : IsGalois ℚ F)
      (ρF : (F ≃ₐ[ℚ] F) →* G),
      Function.Injective ρF ∧ ρF.comp (AlgEquiv.restrictNormalHom F) = ρ := by
  let H : ClosedSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    ⟨ρ.ker, ρ.ker.isClosed_of_isOpen hker⟩
  let F : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.fixedField H.1
  have hfix : F.fixingSubgroup = ρ.ker := InfiniteGalois.fixingSubgroup_fixedField H
  have : FiniteDimensional ℚ F :=
    (InfiniteGalois.isOpen_iff_finite F).mp (by
      change IsOpen (F.fixingSubgroup : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
      rw [hfix]
      exact hker)
  have : NumberField F := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  have : F.fixingSubgroup.Normal := hfix.symm ▸ ρ.normal_ker
  have : IsGalois ℚ F := (InfiniteGalois.normal_iff_isGalois F).mp inferInstance
  let e := InfiniteGalois.normalAutEquivQuotient H
  let ρF : (F ≃ₐ[ℚ] F) →* G :=
    (QuotientGroup.kerLift ρ).comp e.symm.toMonoidHom
  refine ⟨F, inferInstance, inferInstance, ρF, ?_, ?_⟩
  · exact (QuotientGroup.kerLift_injective ρ).comp e.symm.injective
  · ext σ
    change QuotientGroup.kerLift ρ (e.symm (AlgEquiv.restrictNormalHom F σ)) = ρ σ
    rw [← InfiniteGalois.normalAutEquivQuotient_apply H σ]
    change QuotientGroup.kerLift ρ (e.symm (e σ)) = ρ σ
    rw [e.symm_apply_apply]
    exact QuotientGroup.kerLift_mk ρ σ

/-- Continuity into a discrete group supplies the open-kernel hypothesis. -/
theorem exists_faithful_finiteGalois_descent_of_continuous
    {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* G)
    (hρ : Continuous ρ) :
    ∃ (F : IntermediateField ℚ (AlgebraicClosure ℚ))
      (_ : NumberField F) (_ : IsGalois ℚ F)
      (ρF : (F ≃ₐ[ℚ] F) →* G),
      Function.Injective ρF ∧ ρF.comp (AlgEquiv.restrictNormalHom F) = ρ := by
  apply exists_faithful_finiteGalois_descent ρ
  exact (isOpen_discrete ({1} : Set G)).preimage hρ

/-- A finite-level representation with values in any monoid descends faithfully
to a finite Galois number field.  In particular this applies to matrix monoids. -/
theorem exists_faithful_finiteGalois_descent_of_finiteLevel
    {M : Type*} [Monoid M]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* M)
    (hfinite : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        (∀ x ∈ L, σ x = x) → ρ σ = 1) :
    ∃ (F : IntermediateField ℚ (AlgebraicClosure ℚ))
      (_ : NumberField F) (_ : IsGalois ℚ F)
      (ρF : (F ≃ₐ[ℚ] F) →* M),
      Function.Injective ρF ∧ ρF.comp (AlgEquiv.restrictNormalHom F) = ρ := by
  obtain ⟨L, hL, hρL⟩ := hfinite
  have hle : L.fixingSubgroup ≤ ρ.toHomUnits.ker := by
    intro σ hσ
    apply Units.ext
    simpa using hρL σ ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ)
  have hker : IsOpen (ρ.toHomUnits.ker : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :=
    Subgroup.isOpen_mono hle (IntermediateField.fixingSubgroup_isOpen L)
  obtain ⟨F, hF, hGal, ρF, hinj, heq⟩ := exists_faithful_finiteGalois_descent ρ.toHomUnits hker
  exact ⟨F, hF, hGal, (Units.coeHom M).comp ρF,
    Units.val_injective.comp hinj, by ext σ; exact congrArg (fun ψ : _ →* Mˣ => ((ψ σ) : M)) heq⟩

open NumberField FrobeniusDensity in
/-- Unramifiedness of the absolute representation descends to the ideal inertia
groups of its faithful finite Galois realization. -/
theorem inertia_eq_bot_of_descended_unramified
    {M : Type*} [Monoid M]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* M)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]
    (ρF : (F ≃ₐ[ℚ] F) →* M) (hinj : Function.Injective ρF)
    (heq : ρF.comp (AlgEquiv.restrictNormalHom F) = ρ)
    {l : ℕ} (hl : l.Prime)
    (hunr : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime l →
      ∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1)
    (Q : Ideal (𝓞 F)) [Q.IsPrime] [Q.LiesOver (ratPrimeIdeal l)] :
    Q.inertia (F ≃ₐ[ℚ] F) = ⊥ := by
  have : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance (ne_bot_of_liesOver_ratPrimeIdeal hl)
  have hlQ : (l : 𝓞 F) ∈ Q := by
    have h : (l : ℤ) ∈ Q.under ℤ := by
      rw [← Q.over_def (ratPrimeIdeal l)]
      exact Ideal.subset_span (by simp)
    change algebraMap ℤ (𝓞 F) (l : ℤ) ∈ Q at h
    simpa using h
  apply le_antisymm _ bot_le
  intro τ hτ
  rw [Subgroup.mem_bot]
  apply hinj
  rw [map_one]
  obtain ⟨σ, hσ, P, hP, hlP, hσP⟩ :=
    NumberField.exists_lift_mem_inertia_integralClosure F Q hlQ τ hτ
  have : P.IsMaximal := hP
  obtain ⟨A, hlA, hσA⟩ :=
    ValuationSubring.exists_liesOverPrime_mem_inertiaSubgroupIn P hl hlP σ hσP
  rw [← hσ]
  change (ρF.comp (AlgEquiv.restrictNormalHom F)) σ = 1
  rw [heq]
  exact hunr A hlA σ hσA

end HorizontalPadicL

end BundleResidualFiniteDescent

-- From Solutions/ResidualFrobeniusLift.lean
section BundleResidualFrobeniusLift

open scoped NumberField Pointwise

namespace NumberField

/-- A chosen finite arithmetic Frobenius has an absolute arithmetic Frobenius lift,
expressed using the valuation-subring convention for absolute Galois representations. -/
theorem exists_valuation_frobenius_lift_arithFrobAt
    (E : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField E] [IsGalois ℚ E]
    (ℓ : ℕ) (hℓ : ℓ.Prime) (Q : Ideal (𝓞 E)) [Q.IsPrime]
    [Q.LiesOver (FrobeniusDensity.ratPrimeIdeal ℓ)] [Finite (𝓞 E ⧸ Q)] :
    ∃ (A : ValuationSubring (AlgebraicClosure ℚ))
      (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt σ ℓ ∧
      AlgEquiv.restrictNormal σ E = arithFrobAt ℤ (E ≃ₐ[ℚ] E) Q := by
  obtain ⟨Qt, hQt, σ, hQtQ, hσ, hstable, hfrob⟩ :=
    NumberField.exists_isFrobenius_lift_arithFrobAt E ℓ hℓ Q
  let : Qt.IsMaximal := hQt
  let : Qt.LiesOver Q := hQtQ
  have hℓQ : ((ℓ : ℤ) : 𝓞 E) ∈ Q := by
    have hmem := (Ideal.mem_of_liesOver Q (FrobeniusDensity.ratPrimeIdeal ℓ)
      (ℓ : ℤ)).mp (Ideal.mem_span_singleton_self _)
    simpa using hmem
  have hℓQt : (ℓ : 𝓞 (AlgebraicClosure ℚ)) ∈ Qt := by
    have hmem := (Ideal.mem_of_liesOver Qt Q ((ℓ : ℤ) : 𝓞 E)).mp hℓQ
    simpa using hmem
  obtain ⟨A, hA⟩ := NumberField.exists_valuationSubring_eq_localization Qt
  obtain ⟨hAlies, hAfrob⟩ :=
    ValuationSubring.isFrobeniusAt_of_forall_smul_sub_pow_mem
      Qt ℓ hℓ hℓQt σ hstable hfrob A hA
  exact ⟨A, σ, hAlies, hAfrob, hσ⟩

end NumberField

end BundleResidualFrobeniusLift

-- From Solutions/ResidualGaloisSolution.lean
noncomputable section BundleResidualGaloisSolution

open NumberField HorizontalPadicL FrobeniusDensity

theorem solution {N k p : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (ιp : MTT.Qbar →+* ℂ_[p]) :
    Nonempty (EigenformResidualGaloisRepresentationData hN hk f ιp) := by
  obtain ⟨ρ, hfinite, hunram, hfrob⟩ :=
    f.exists_residual_matrix_representation hN hk ι ιp
  obtain ⟨F, hF, hGal, ρF, hinj, heq⟩ :=
    exists_faithful_finiteGalois_descent_of_finiteLevel ρ hfinite
  let : NumberField F := hF
  let : IsGalois ℚ F := hGal
  have hfrobF (l : ℕ) (hl : l.Prime) (hlNp : Nat.Coprime l (N * p))
      (Q : Ideal (𝓞 F)) [Q.IsPrime] [Q.LiesOver (ratPrimeIdeal l)]
      [Finite (𝓞 F ⧸ Q)] :
      Matrix.trace (ρF (arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q)) =
          Ideal.Quotient.mk (f.coefficientPrime ιp) (f.integralCoeff hN hk l) ∧
        Matrix.det (ρF (arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q)) =
          Ideal.Quotient.mk (f.coefficientPrime ιp)
            (f.integralNebentype (l : ZMod N) *
              (l : 𝓞 f.coefficientField) ^ (k - 1)) := by
    obtain ⟨A, σ, hA, hσ, hrestrict⟩ :=
      NumberField.exists_valuation_frobenius_lift_arithFrobAt F l hl Q
    have hvalue : ρF (arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q) = ρ σ := by
      rw [← hrestrict]
      exact congrArg (fun ψ ↦ ψ σ) heq
    rw [hvalue]
    exact hfrob l hl hlNp A hA σ hσ
  refine ⟨{
    kernelField := F
    representation := ρF
    faithful := hinj
    unramified_outside := ?_
    trace_frobenius := ?_
    det_frobenius := ?_ }⟩
  · intro l hl hlNp Q hQ hQlies
    let : Q.IsPrime := hQ
    let : Q.LiesOver (ratPrimeIdeal l) := hQlies
    exact inertia_eq_bot_of_descended_unramified ρ F ρF hinj heq hl
      (hunram l hl hlNp) Q
  · intro l hl hlNp Q hQ hQlies
    let : Q.IsPrime := hQ
    let : Q.LiesOver (ratPrimeIdeal l) := hQlies
    let : Finite (𝓞 F ⧸ Q) := finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hl)
    exact (hfrobF l hl hlNp Q).1
  · intro l hl hlNp Q hQ hQlies
    let : Q.IsPrime := hQ
    let : Q.LiesOver (ratPrimeIdeal l) := hQlies
    let : Finite (𝓞 F ⧸ Q) := finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hl)
    exact (hfrobF l hl hlNp Q).2

end BundleResidualGaloisSolution

end privateSection

public section publicSection

noncomputable section

namespace HorizontalPadicL

/-- **This is a formalization of a standard textbook result, so should be
low-priority.**

Deligne's residual Galois representation attached to a normalized
eigenform and a chosen `p`-adic embedding.  Its coefficient field is
`f.coefficientField`, its prime is the canonically defined
`f.coefficientPrime ιp`, and its target is the resulting finite residue field
`EigenformResidueField f ιp`; none of these are auxiliary choices in
the existence statement. -/
theorem eigenform_residualGaloisRepresentation_exists_v2
    {N k p : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (ιp : MTT.Qbar →+* ℂ_[p]) :
    Nonempty (EigenformResidualGaloisRepresentationData hN hk f ιp) := _root_.solution hN hk ι f ιp

end HorizontalPadicL
end

end publicSection
