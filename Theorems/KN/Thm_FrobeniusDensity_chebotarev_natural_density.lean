module

public import Definitions.FLT.Def_LanglandsTunnell_TowerCounting
public import Mathlib.Topology.Instances.Real.Lemmas

import TauCeti.NumberTheory.Chebotarev.PrimeCounting.FrobeniusPrimeCount
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import TauCeti.NumberTheory.NumberField.Frobenius.DecompositionGroup
import TauCeti.NumberTheory.RamificationInertia.Galois
import Mathlib.Tactic

section privateSection

open NumberField Ideal Filter Topology IsDedekindDomain

private theorem under_ratPrime (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.asIdeal.under ℤ =
      FrobeniusDensity.ratPrimeIdeal (Rat.HeightOneSpectrum.natGenerator v) := by
  rw [Ideal.under_def, Rat.algebraMap_int_ringOfIntegers_eq]
  have he : Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) = Rat.ringOfIntegersEquiv := by
    ext x
    exact Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv x
  have hmap : v.asIdeal.comap (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) =
      v.asIdeal.map Rat.ringOfIntegersEquiv := by
    exact Ideal.comap_symm Rat.ringOfIntegersEquiv
  rw [hmap]
  simpa [he] using (Rat.HeightOneSpectrum.span_natGenerator v).symm

/-- KN's chosen arithmetic Frobenius has the same class as Tau Ceti's Artin symbol. -/
private theorem indicator_iff (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (σ : L ≃ₐ[ℚ] L) (v : HeightOneSpectrum (𝓞 ℚ)) :
    LanglandsTunnell.classIndicator σ (Rat.HeightOneSpectrum.natGenerator v) = 1 ↔
      v ∈ NumberField.Chebotarev.frobeniusPrimeSet ℚ L (ConjClasses.mk σ) := by
  classical
  rw [LanglandsTunnell.classIndicator]
  simp only [ite_eq_left_iff, zero_ne_one, imp_false, not_not]
  constructor
  · rintro ⟨hp, Q, hQ, hOver, hInertia, hConj⟩
    let := hQ
    let := hOver
    have : Q.LiesOver v.asIdeal := by
      rw [Ideal.liesOver_iff, Ideal.under_ringOfIntegers_rat_eq_map, ← hOver.over,
        ← under_ratPrime v, Ideal.under_def,
        Ideal.map_comap_of_surjective _ Rat.algebraMap_int_ringOfIntegers_bijective.surjective]
    let : Algebra.IsUnramifiedAt (𝓞 ℚ) Q :=
      (Ideal.isUnramifiedAt_iff_inertia_eq_bot Q).mpr hInertia
    have hur : ∀ (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver v.asIdeal],
        Algebra.IsUnramifiedAt (𝓞 ℚ) P := fun P _ _ =>
      Ideal.isUnramifiedAt_of_isUnramifiedAt_of_isGaloisGroup v.asIdeal Q P (L ≃ₐ[ℚ] L)
    let : Finite (𝓞 L ⧸ Q) :=
      FrobeniusDensity.finite_quotient_of_ne_bot
        (FrobeniusDensity.ne_bot_of_liesOver_ratPrimeIdeal hp)
    refine (NumberField.Chebotarev.mem_frobeniusPrimeSet_iff).mpr ⟨hur, ?_⟩
    rw [NumberField.artinSymbol_eq_mk_of_isArithFrobAt v.asIdeal hur Q
      (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)
      ((Ideal.isArithFrobAt_ringOfIntegers_rat_iff _ _).mpr
        (IsArithFrobAt.arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q))]
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr hConj.symm
  · intro hv
    obtain ⟨Q, hFrob⟩ :=
      NumberField.Chebotarev.exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk hv
    let : Q.1.IsPrime := Q.2.1
    let : Q.1.LiesOver v.asIdeal := Q.2.2
    have : Q.1.LiesOver (FrobeniusDensity.ratPrimeIdeal
        (Rat.HeightOneSpectrum.natGenerator v)) := by
      rw [← under_ratPrime v]
      exact Ideal.LiesOver.trans Q.1 v.asIdeal (v.asIdeal.under ℤ)
    let : Algebra.IsUnramifiedAt (𝓞 ℚ) Q.1 :=
      NumberField.Chebotarev.isUnramifiedAt_of_mem_frobeniusPrimeSet hv Q.1
    let : Finite (𝓞 L ⧸ Q.1) :=
      FrobeniusDensity.finite_quotient_of_ne_bot
        (FrobeniusDensity.ne_bot_of_liesOver_ratPrimeIdeal
          (Rat.HeightOneSpectrum.prime_natGenerator v))
    have hInertia := (Ideal.isUnramifiedAt_iff_inertia_eq_bot (K := ℚ) Q.1).mp inferInstance
    refine ⟨Rat.HeightOneSpectrum.prime_natGenerator v, Q.1, inferInstance,
      inferInstance, hInertia, ?_⟩
    have heq : σ = arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q.1 := by
      have hmul := ((Ideal.isArithFrobAt_ringOfIntegers_rat_iff _ _).mp hFrob).mul_inv_mem_inertia
        (IsArithFrobAt.arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q.1)
      rw [hInertia, Subgroup.mem_bot] at hmul
      exact mul_inv_eq_one.mp hmul
    rw [heq]

private theorem natGenerator_injective :
    Function.Injective (Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ)) := by
  intro v w h
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  exact Subtype.ext h

/-- Transport Tau Ceti's inclusive ideal count to KN's strict natural-number cutoff. -/
private theorem count_transport (A : Set (HeightOneSpectrum (𝓞 ℚ))) (P : ℕ → Prop)
    [DecidablePred P]
    (hP : ∀ p, P p ↔ ∃ v : HeightOneSpectrum (𝓞 ℚ),
      Rat.HeightOneSpectrum.natGenerator v = p ∧ v ∈ A)
    (X : ℕ) :
    TauCeti.primeCount ℚ A ((X : ℝ) - 1) =
      (((Finset.range X).filter P).card : ℝ) := by
  classical
  rw [TauCeti.primeCount_eq_card]
  congr 1
  apply Finset.card_bij (fun v _ => Rat.HeightOneSpectrum.natGenerator v)
  · intro v hv
    obtain ⟨hvX, hvA⟩ := Finset.mem_filter.mp hv
    have hvle := (TauCeti.mem_normLE _).mp hvX
    rw [Rat.HeightOneSpectrum.absNorm_asIdeal] at hvle
    have hvlt : Rat.HeightOneSpectrum.natGenerator v < X := by
      have : (Rat.HeightOneSpectrum.natGenerator v : ℝ) < X := by linarith
      exact_mod_cast this
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hvlt, (hP _).mpr ⟨v, rfl, hvA⟩⟩
  · intro v _ w _ h
    exact natGenerator_injective h
  · intro p hp
    obtain ⟨hpX, hpP⟩ := Finset.mem_filter.mp hp
    obtain ⟨v, hv, hvA⟩ := (hP p).mp hpP
    refine ⟨v, Finset.mem_filter.mpr ⟨?_, hvA⟩, hv⟩
    apply (TauCeti.mem_normLE _).mpr
    rw [Rat.HeightOneSpectrum.absNorm_asIdeal, hv]
    have hpX := Finset.mem_range.mp hpX
    have hle : p + 1 ≤ X := hpX
    have hleR : (p : ℝ) + 1 ≤ X := by exact_mod_cast hle
    linarith

private theorem density_bridge (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (σ : L ≃ₐ[ℚ] L) (S : Finset ℕ) :
    Tendsto
      (fun X : ℕ =>
        (((Finset.range X).filter fun p =>
            p ∉ S ∧ LanglandsTunnell.classIndicator σ p = 1).card : ℝ) /
          (((Finset.range X).filter Nat.Prime).card : ℝ))
      atTop
      (𝓝 ((Nat.card {τ : L ≃ₐ[ℚ] L | IsConj σ τ} : ℝ) /
        (Nat.card (L ≃ₐ[ℚ] L) : ℝ))) := by
  classical
  let C := ConjClasses.mk σ
  let F := NumberField.Chebotarev.frobeniusPrimeSet ℚ L C
  let A : Set (HeightOneSpectrum (𝓞 ℚ)) :=
    {v | Rat.HeightOneSpectrum.natGenerator v ∉ S ∧ v ∈ F}
  have hf : (symmDiff A F).Finite := by
    have hfin : (Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ) ⁻¹' (S : Set ℕ)).Finite :=
      S.finite_toSet.preimage natGenerator_injective.injOn
    apply hfin.subset
    intro v hv
    simp only [Set.mem_symmDiff, A, Set.mem_ofPred_eq] at hv
    change Rat.HeightOneSpectrum.natGenerator v ∈ S
    tauto
  have hd :=
    (NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet ℚ L C).of_finite_symmDiff hf
  have hclass : C.carrier = {τ : L ≃ₐ[ℚ] L | IsConj σ τ} := by
    ext τ
    simp only [C, ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj,
      Set.mem_ofPred_eq, isConj_comm]
  rw [NumberField.Set.hasNaturalDensity_def, hclass] at hd
  have hcut : Tendsto (fun X : ℕ => (X : ℝ) - 1) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_natCast_atTop_atTop
  apply (hd.comp hcut).congr'
  filter_upwards [] with X
  dsimp only [Function.comp_def]
  rw [count_transport A (fun p => p ∉ S ∧ LanglandsTunnell.classIndicator σ p = 1)
    (fun p => ?_) X, count_transport Set.univ Nat.Prime (fun p => ?_) X]
  · constructor
    · intro hp
      obtain ⟨v, hv⟩ := Rat.HeightOneSpectrum.exists_absNorm_eq hp
      exact ⟨v, (Rat.HeightOneSpectrum.absNorm_asIdeal v).symm.trans hv, Set.mem_univ v⟩
    · rintro ⟨v, hv, _⟩
      exact hv ▸ Rat.HeightOneSpectrum.prime_natGenerator v
  · constructor
    · rintro ⟨hpS, hpI⟩
      have hp : p.Prime := by
        by_contra hnp
        simp [LanglandsTunnell.classIndicator, hnp] at hpI
      obtain ⟨v, hv⟩ := Rat.HeightOneSpectrum.exists_absNorm_eq hp
      rw [Rat.HeightOneSpectrum.absNorm_asIdeal] at hv
      refine ⟨v, hv, ?_⟩
      change Rat.HeightOneSpectrum.natGenerator v ∉ S ∧ v ∈ F
      refine ⟨hv ▸ hpS, ?_⟩
      apply (indicator_iff L σ v).mp
      simpa only [hv] using hpI
    · rintro ⟨v, hv, hvA⟩
      obtain ⟨hvS, hvF⟩ := hvA
      refine ⟨hv ▸ hvS, ?_⟩
      simpa only [hv] using (indicator_iff L σ v).mpr hvF

end privateSection

public section publicSection

open NumberField Ideal Filter Topology

namespace FrobeniusDensity

/-- Chebotarev's density theorem over `ℚ`, stated as natural density relative to the
rational primes and allowing an arbitrary finite set of excluded residue characteristics. -/
theorem chebotarev_natural_density
    (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (σ : L ≃ₐ[ℚ] L) (S : Finset ℕ) :
    Tendsto
      (fun X : ℕ =>
        (((Finset.range X).filter fun ℓ =>
            ℓ ∉ S ∧ LanglandsTunnell.classIndicator σ ℓ = 1).card : ℝ) /
          (((Finset.range X).filter Nat.Prime).card : ℝ))
      atTop
      (𝓝 ((Nat.card {τ : L ≃ₐ[ℚ] L | IsConj σ τ} : ℝ) /
        (Nat.card (L ≃ₐ[ℚ] L) : ℝ))) := density_bridge L σ S

end FrobeniusDensity

end publicSection
