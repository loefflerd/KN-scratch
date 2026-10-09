module

public import Definitions.FLT.Def_FLTPrelim_Modularity
public import Definitions.KN.Def_KN_HorizontalPadicL

import Theorems.KN.Thm_WeierstrassCurve_minimal_baseChange_completion
import Theorems.KN.Thm_HorizontalPadicL_goodReduction_minimal_of_not_modularConductor_dvd
import Definitions.FLT.Def_WeierstrassCurve_VariableChangePointEquiv
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

section privateSection

open WeierstrassCurve IsDedekindDomain NumberField IsLocalRing

namespace IntegralModelTransferAux

def coefficients (E : WeierstrassCurve ℚ) : Fin 5 → ℚ :=
  ![E.a₁, E.a₂, E.a₃, E.a₄, E.a₆]

lemma prime_to_common_denominator (v : HeightOneSpectrum (𝓞 ℚ))
    (E : WeierstrassCurve ℚ) [E.IsIntegral (v.valuationSubringAtPrime ℚ)] :
    ∃ d : ℕ, d ≠ 0 ∧ ¬ (Rat.HeightOneSpectrum.primesEquiv v).val ∣ d ∧
      ∀ i, ∃ n : ℤ, (d : ℚ) * coefficients E i = n := by
  classical
  let p := (Rat.HeightOneSpectrum.primesEquiv v).val
  have hp : p.Prime := (Rat.HeightOneSpectrum.primesEquiv v).property
  have : Fact p.Prime := ⟨hp⟩
  have hcoeff (i : Fin 5) : v.valuation ℚ (coefficients E i) ≤ 1 := by
    have heq := baseChange_integralModel_eq (v.valuationSubringAtPrime ℚ) E
    rw [← heq]
    fin_cases i <;> simp only [coefficients, baseChange, map_a₁, map_a₂, map_a₃,
      map_a₄, map_a₆]
    all_goals
      change _ ∈ (v.valuation ℚ).valuationSubring
      rw [← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      first
        | exact (integralModel (v.valuationSubringAtPrime ℚ) E).a₁.property
        | exact (integralModel (v.valuationSubringAtPrime ℚ) E).a₂.property
        | exact (integralModel (v.valuationSubringAtPrime ℚ) E).a₃.property
        | exact (integralModel (v.valuationSubringAtPrime ℚ) E).a₄.property
        | exact (integralModel (v.valuationSubringAtPrime ℚ) E).a₆.property
  have hden (i : Fin 5) : ¬ p ∣ (coefficients E i).den := by
    apply Rat.padicValuation_le_one_iff.mp
    exact (Rat.HeightOneSpectrum.valuation_equiv_padicValuation v).le_one_iff_le_one.mp
      (hcoeff i)
  let d := ∏ i : Fin 5, (coefficients E i).den
  refine ⟨d, Finset.prod_ne_zero_iff.mpr (fun i _ => Rat.den_nz _), ?_, ?_⟩
  · intro h
    obtain ⟨i, _, hi⟩ := (Nat.prime_iff.mp hp).exists_mem_finset_dvd h
    exact hden i hi
  · intro i
    obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem (fun i : Fin 5 => (coefficients E i).den)
      (Finset.mem_univ i)
    refine ⟨b * (coefficients E i).num, ?_⟩
    dsimp only [d]
    rw [hb, Nat.cast_mul, mul_comm ((coefficients E i).den : ℚ), mul_assoc,
      Rat.den_mul_eq_num, Int.cast_mul, Int.cast_natCast]

lemma clear_integral_model (v : HeightOneSpectrum (𝓞 ℚ))
    (E : WeierstrassCurve ℚ) [E.IsIntegral (v.valuationSubringAtPrime ℚ)] :
    ∃ (W : WeierstrassCurve ℤ) (C : VariableChange ℚ),
      W.baseChange ℚ = C • E ∧ v.valuation ℚ (C.u : ℚ) = 1 := by
  classical
  obtain ⟨d, hd, hpd, hn⟩ := prime_to_common_denominator v E
  choose n hn using hn
  let W : WeierstrassCurve ℤ :=
    ⟨n 0, (d : ℤ) * n 1, (d : ℤ) ^ 2 * n 2, (d : ℤ) ^ 3 * n 3,
      (d : ℤ) ^ 5 * n 4⟩
  have hdq : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  let C : VariableChange ℚ := ⟨(Units.mk0 (d : ℚ) hdq)⁻¹, 0, 0, 0⟩
  refine ⟨W, C, ?_, ?_⟩
  · ext <;> simp [W, C, variableChange_def, ← hn 0, ← hn 1, ← hn 2, ← hn 3,
      ← hn 4, coefficients] <;> ring
  · let p := (Rat.HeightOneSpectrum.primesEquiv v).val
    have : Fact p.Prime := ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
    have hpad : Rat.padicValuation p (d : ℚ) = 1 := by
      have h := Int.padicValuation_eq_one_iff (p := p) (x := (d : ℤ))
      simpa [Rat.padicValuation_natCast] using
        h.mpr (by simpa only [Int.natCast_dvd_natCast, p] using hpd)
    have hval : v.valuation ℚ (d : ℚ) = 1 :=
      (Rat.HeightOneSpectrum.valuation_equiv_padicValuation v).eq_one_iff_eq_one.mpr hpad
    simp [C, map_inv₀, hval]

lemma minimal_discriminant_eq {R K : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (E : WeierstrassCurve K) (C : VariableChange K)
    [E.IsMinimal R] [(C • E).IsMinimal R] :
    (IsDiscreteValuationRing.maximalIdeal R).valuation K (C • E).Δ =
      (IsDiscreteValuationRing.maximalIdeal R).valuation K E.Δ := by
  have upper (W : WeierstrassCurve K) [W.IsMinimal R] (D : VariableChange K)
      [(D • W).IsIntegral R] : valuation_Δ_aux R (D • W) ≤ valuation_Δ_aux R W := by
    rcases le_total (valuation_Δ_aux R (D • W)) (valuation_Δ_aux R W) with h | h
    · exact h
    · simpa using (IsMinimal.val_Δ_maximal (R := R) (W := W)).2 inferInstance
        (by simpa using h)
  have h₁ := upper E C
  have : (C⁻¹ • C • E).IsIntegral R := by simpa using (inferInstance : E.IsIntegral R)
  have h₂ := upper (C • E) C⁻¹
  have haux : valuation_Δ_aux R (C • E) = valuation_Δ_aux R E :=
    le_antisymm h₁ (by simpa using h₂)
  have hcoe := congrArg Subtype.val haux
  simpa only [valuation_Δ_aux_eq_of_isIntegral] using hcoe

lemma minimal_discriminant_le {R K : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (E : WeierstrassCurve K) (C : VariableChange K)
    [E.IsMinimal R] [(C • E).IsIntegral R] :
    (IsDiscreteValuationRing.maximalIdeal R).valuation K (C • E).Δ ≤
      (IsDiscreteValuationRing.maximalIdeal R).valuation K E.Δ := by
  have h : valuation_Δ_aux R (C • E) ≤ valuation_Δ_aux R E := by
    rcases le_total (valuation_Δ_aux R (C • E)) (valuation_Δ_aux R E) with h | h
    · exact h
    · simpa using (IsMinimal.val_Δ_maximal (R := R) (W := E)).2 inferInstance
        (by simpa using h)
  have hcoe : (valuation_Δ_aux R (C • E) : WithZero (Multiplicative ℤ)) ≤
      (valuation_Δ_aux R E : WithZero (Multiplicative ℤ)) := h
  simpa only [valuation_Δ_aux_eq_of_isIntegral] using hcoe

lemma minimal_of_discriminant_eq {R K : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (E : WeierstrassCurve K) (C : VariableChange K)
    [E.IsMinimal R] [(C • E).IsIntegral R]
    (h : (IsDiscreteValuationRing.maximalIdeal R).valuation K (C • E).Δ =
      (IsDiscreteValuationRing.maximalIdeal R).valuation K E.Δ) :
    (C • E).IsMinimal R := by
  constructor
  refine ⟨by simpa, ?_⟩
  intro D hD _
  have : (D • C • E).IsIntegral R := hD
  have : ((D * C) • E).IsIntegral R := by simpa [mul_smul] using hD
  have hd := minimal_discriminant_le (R := R) E (D * C)
  change (valuation_Δ_aux R (D • C • E) : WithZero (Multiplicative ℤ)) ≤
    (valuation_Δ_aux R (1 • C • E) : WithZero (Multiplicative ℤ))
  simp only [one_smul, valuation_Δ_aux_eq_of_isIntegral, h]
  simpa only [mul_smul] using hd

lemma normalized_integers {R K : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] :
    ((IsDiscreteValuationRing.maximalIdeal R).valuation K).Integers R where
  hom_inj := FaithfulSMul.algebraMap_injective R K
  map_le_one := HeightOneSpectrum.valuation_le_one _
  exists_of_le_one := by
    intro x hx
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one K x
    intro q
    have hq : q = IsDiscreteValuationRing.maximalIdeal R :=
      HeightOneSpectrum.ext_iff.mpr (IsLocalRing.eq_maximalIdeal q.isMaximal)
    simpa [hq] using hx

lemma normalized_isEquiv {R K Γ : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) (hw : w.Integers R) :
    ((IsDiscreteValuationRing.maximalIdeal R).valuation K).IsEquiv w := by
  apply Valuation.isEquiv_of_val_le_one
  intro x
  constructor
  · intro hx
    obtain ⟨r, rfl⟩ := (normalized_integers (R := R) (K := K)).exists_of_le_one hx
    exact hw.map_le_one r
  · intro hx
    obtain ⟨r, rfl⟩ := hw.exists_of_le_one hx
    exact HeightOneSpectrum.valuation_le_one _ r

lemma integral_int_baseChange (W : WeierstrassCurve ℤ) {K : Type*} [Field K]
    [Algebra ℤ K]
    (S : ValuationSubring K) : (W.baseChange K).IsIntegral S := by
  apply isIntegral_of_exists_lift S
  · exact ⟨(W.a₁ : S), by simp [baseChange]⟩
  · exact ⟨(W.a₂ : S), by simp [baseChange]⟩
  · exact ⟨(W.a₃ : S), by simp [baseChange]⟩
  · exact ⟨(W.a₄ : S), by simp [baseChange]⟩
  · exact ⟨(W.a₆ : S), by simp [baseChange]⟩

lemma card_map_equiv {F G : Type*} [Field F] [Field G]
    (E : WeierstrassCurve F) (φ : F ≃+* G) :
    Nat.card (E.map φ.toRingHom).toAffine.Point = Nat.card E.toAffine.Point := by
  let e : {xy : F × F // E.toAffine.Nonsingular xy.1 xy.2} ≃
      {xy : G × G // (E.map φ.toRingHom).toAffine.Nonsingular xy.1 xy.2} :=
    (φ.toEquiv.prodCongr φ.toEquiv).subtypeEquiv (by
      intro xy
      exact (E.toAffine.map_nonsingular φ.injective xy.1 xy.2).symm)
  exact Nat.card_congr ((Affine.nonsingularPointEquiv E.toAffine).trans
    (e.optionCongr.trans
      (Affine.nonsingularPointEquiv (E.map φ.toRingHom).toAffine).symm)).symm

lemma completion_valuation (v : HeightOneSpectrum (𝓞 ℚ)) (a : ℚ) :
    Valued.v (algebraMap ℚ (v.adicCompletion ℚ) a) = v.valuation ℚ a := by
  simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

lemma exists_integral_model_minimal_completion (E : WeierstrassCurve ℚ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ (W : WeierstrassCurve ℤ) (C : VariableChange ℚ),
      W.baseChange ℚ = C • E ∧
      (W.baseChange (v.adicCompletion ℚ)).IsMinimal (v.adicCompletionIntegers ℚ) := by
  classical
  let R := v.valuationSubringAtPrime ℚ
  let K := v.adicCompletion ℚ
  let S := v.adicCompletionIntegers ℚ
  have : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 ℚ) v.ne_bot R
  obtain ⟨C₀, h₀, h₀K⟩ := E.exists_minimal_rational_model_and_completion v
  have : (C₀ • E).IsMinimal R := h₀
  have : ((C₀ • E).baseChange K).IsMinimal S := h₀K
  obtain ⟨W, C₁, hW, hu⟩ := clear_integral_model v (C₀ • E)
  have hWQ : W.baseChange ℚ = (C₁ * C₀) • E := by
    simpa [mul_smul] using hW
  have hWK : W.baseChange K = C₁.baseChange K • (C₀ • E).baseChange K := by
    have heq := congrArg (fun V : WeierstrassCurve ℚ => V.baseChange K) hW
    simpa only [baseChange, VariableChange.baseChange, map_map, ← map_variableChange,
      IsScalarTower.algebraMap_eq ℤ ℚ K] using heq
  have : (W.baseChange K).IsIntegral S := integral_int_baseChange W S
  have : (C₁.baseChange K • (C₀ • E).baseChange K).IsIntegral S := hWK ▸ inferInstance
  have eS := normalized_isEquiv (Valued.v : Valuation K (WithZero (Multiplicative ℤ)))
    (HeightOneSpectrum.adicCompletionIntegers.integers ℚ v)
  have huK : (IsDiscreteValuationRing.maximalIdeal S).valuation K
      (C₁.baseChange K).u = 1 := by
    apply eS.eq_one_iff_eq_one.mpr
    change Valued.v (algebraMap ℚ K (C₁.u : ℚ)) = 1
    rw [completion_valuation, hu]
  have hdelta : (IsDiscreteValuationRing.maximalIdeal S).valuation K
      (C₁.baseChange K • (C₀ • E).baseChange K).Δ =
      (IsDiscreteValuationRing.maximalIdeal S).valuation K ((C₀ • E).baseChange K).Δ := by
    simp only [variableChange_Δ, map_mul, map_pow, Units.val_inv_eq_inv_val,
      map_inv₀, huK, inv_one, one_pow, one_mul]
  have hmin := minimal_of_discriminant_eq (R := S)
    ((C₀ • E).baseChange K) (C₁.baseChange K) hdelta
  exact ⟨W, C₁ * C₀, hWQ, hWK ▸ hmin⟩

lemma integralModel_int_eq (W : WeierstrassCurve ℤ) {K : Type*} [Field K]
    [Algebra ℤ K]
    (S : ValuationSubring K) [(W.baseChange K).IsIntegral S] :
    integralModel S (W.baseChange K) = W.baseChange S := by
  apply WeierstrassCurve.map_injective (FaithfulSMul.algebraMap_injective S K)
  dsimp only
  change (integralModel S (W.baseChange K)).baseChange K = (W.baseChange S).baseChange K
  rw [baseChange_integralModel_eq]
  ext <;> simp [baseChange]

lemma reduction_int_card (W : WeierstrassCurve ℤ) (v : HeightOneSpectrum (𝓞 ℚ))
    [(W.baseChange (v.adicCompletion ℚ)).IsMinimal (v.adicCompletionIntegers ℚ)] :
    Nat.card ((W.baseChange (v.adicCompletion ℚ)).reduction
      (v.adicCompletionIntegers ℚ)).toAffine.Point =
      Nat.card (W.reductionMod (Rat.HeightOneSpectrum.primesEquiv v).val).toAffine.Point := by
  classical
  let p := (Rat.HeightOneSpectrum.primesEquiv v).val
  have : Fact p.Prime := ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  let S := v.adicCompletionIntegers ℚ
  let φ : ResidueField S ≃+* ZMod p :=
    RingEquiv.trans (ResidueField.mapEquiv
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv)
        PadicInt.residueField
  have hcurve : ((W.baseChange (v.adicCompletion ℚ)).reduction S).map φ.toRingHom =
      W.reductionMod p := by
    rw [reduction, integralModel_int_eq]
    simp only [baseChange, map_map, reductionMod]
    congr 1
    ext n
    simp
  rw [← hcurve]
  exact (card_map_equiv _ φ).symm

lemma minimal_change_descends {R K : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (E : WeierstrassCurve K) [E.IsElliptic] (C : VariableChange K)
    [E.IsMinimal R] [(C • E).IsMinimal R] :
    ∃ D : VariableChange R, D.baseChange K = C := by
  let w := (IsDiscreteValuationRing.maximalIdeal R).valuation K
  have hdelta := minimal_discriminant_eq (R := R) E C
  have hd : w E.Δ ≠ 0 := w.ne_zero_iff.mpr E.isUnit_Δ.ne_zero
  have hpow : (w (C.u : K))⁻¹ ^ 12 = 1 := by
    apply mul_right_cancel₀ hd
    simpa only [one_mul, w, variableChange_Δ, map_mul, map_pow,
      Units.val_inv_eq_inv_val, map_inv₀] using hdelta
  have huval : w (C.u : K) = 1 := by
    have h := (pow_eq_one_iff_of_nonneg zero_le (by decide : 12 ≠ 0)).mp hpow
    exact inv_eq_one.mp h
  obtain ⟨r, hr⟩ := (normalized_integers (R := R) (K := K)).exists_of_le_one huval.le
  have hrunit : IsUnit r :=
    (Valuation.Integers.isUnit_iff_valuation_eq_one
      (normalized_integers (R := R) (K := K))).mpr (by simpa [hr] using huval)
  exact variableChange_integral_of_u_integral (R := R) (W := E)
    (W' := C • E) rfl (u := hrunit.unit) (by simpa using hr)

lemma minimal_reduction_card_eq {R K : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (E : WeierstrassCurve K) [E.IsElliptic] (C : VariableChange K)
    [E.IsMinimal R] [(C • E).IsMinimal R] :
    Nat.card ((C • E).reduction R).toAffine.Point =
      Nat.card (E.reduction R).toAffine.Point := by
  obtain ⟨D, hD⟩ := minimal_change_descends (R := R) E C
  have hint : integralModel R (C • E) = D • integralModel R E := by
    apply WeierstrassCurve.map_injective (FaithfulSMul.algebraMap_injective R K)
    dsimp only
    rw [← map_variableChange]
    change (integralModel R (C • E)).baseChange K =
      D.baseChange K • (integralModel R E).baseChange K
    rw [baseChange_integralModel_eq, hD, baseChange_integralModel_eq]
  have hred : (C • E).reduction R = D.map (residue R) • E.reduction R := by
    simp only [reduction, hint, ← map_variableChange]
  rw [hred]
  exact Nat.card_congr (Affine.Point.variableChangeEquiv (D.map (residue R))
    (E.reduction R).toAffine)

lemma solution (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hmod : HorizontalPadicL.IsModular E) (v : HeightOneSpectrum (𝓞 ℚ))
    (hN : ¬ (Rat.HeightOneSpectrum.primesEquiv v).val ∣
      HorizontalPadicL.modularConductor E hmod) :
    ∃ W : WeierstrassCurve ℤ, W.IsIntegralModelOf E ∧
      W.IsGoodPrimeFor (Rat.HeightOneSpectrum.primesEquiv v).val ∧
      W.apOfModel (Rat.HeightOneSpectrum.primesEquiv v).val =
        E.LFunction (Rat.HeightOneSpectrum.primesEquiv v).val := by
  classical
  let K := v.adicCompletion ℚ
  let S := v.adicCompletionIntegers ℚ
  let p := (Rat.HeightOneSpectrum.primesEquiv v).val
  have : Fact p.Prime := ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  obtain ⟨W, C, hWQ, hmin⟩ := exists_integral_model_minimal_completion E v
  let V := W.baseChange K
  have : V.IsMinimal S := hmin
  have : (E.baseChange K).IsElliptic := by
    change (E.map (algebraMap ℚ K)).IsElliptic
    infer_instance
  have hVC : V = C.baseChange K • E.baseChange K := by
    have h := congrArg (fun E : WeierstrassCurve ℚ => E.baseChange K) hWQ
    simpa only [V, baseChange, VariableChange.baseChange, map_map,
      ← map_variableChange, IsScalarTower.algebraMap_eq ℤ ℚ K] using h
  have : V.IsElliptic := by rw [hVC]; infer_instance
  let A := ((E.baseChange K).exists_isMinimal S).choose
  let D : VariableChange K := A * (C.baseChange K)⁻¹
  have hDV : D • V = (E.baseChange K).minimal S := by
    rw [hVC]
    change (A * (C.baseChange K)⁻¹) • (C.baseChange K • E.baseChange K) =
      A • E.baseChange K
    simp [mul_smul]
  have : (D • V).IsMinimal S := hDV.symm ▸ inferInstance
  have hgood := (HorizontalPadicL.not_modularConductor_dvd_iff_hasGoodReduction_minimal
    E hmod v).mp hN
  have : ((E.baseChange K).minimal S).HasGoodReduction S := hgood
  have hdelta := minimal_discriminant_eq (R := S) V D
  rw [hDV] at hdelta
  have hunit : (IsDiscreteValuationRing.maximalIdeal S).valuation K V.Δ = 1 := by
    rw [← hdelta]
    exact HasGoodReduction.goodReduction (R := S) (W := (E.baseChange K).minimal S)
  have eS := normalized_isEquiv (Valued.v : Valuation K (WithZero (Multiplicative ℤ)))
    (HeightOneSpectrum.adicCompletionIntegers.integers ℚ v)
  have hunitV : Valued.v V.Δ = 1 := eS.eq_one_iff_eq_one.mp hunit
  have hmapΔ : V.Δ = algebraMap ℚ K (W.Δ : ℚ) := by
    simp [V, baseChange, map_Δ]
  rw [hmapΔ, completion_valuation] at hunitV
  have hpad : Rat.padicValuation p (W.Δ : ℚ) = 1 :=
    (Rat.HeightOneSpectrum.valuation_equiv_padicValuation v).eq_one_iff_eq_one.mp hunitV
  have hWgood : W.IsGoodPrimeFor p := by
    apply Int.padicValuation_eq_one_iff.mp
    simpa only [Rat.padicValuation_cast] using hpad
  have hcard := minimal_reduction_card_eq (R := S) V D
  simp only [hDV] at hcard
  refine ⟨W, ⟨C, hWQ.symm⟩, hWgood, ?_⟩
  unfold apOfModel traceOfFrobenius card
  rw [Nat.card_zmod, ← reduction_int_card W v, ← hcard]
  exact (HorizontalPadicL.LFunction_prime_eq_trace_minimal_reduction E v hgood).symm

end IntegralModelTransferAux

end privateSection

public section publicSection

namespace HorizontalPadicL

open NumberField IsDedekindDomain

/-- At each prime outside the modular conductor, choose an integral model with good
reduction whose Frobenius trace is the corresponding coefficient of the global L-series.
The model may depend on the prime; no global minimal-model theorem is required. -/
theorem exists_good_integral_model_with_ap (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hmod : IsModular E) (ℓ : ℕ) (hℓ : ℓ.Prime) (hN : ¬ ℓ ∣ modularConductor E hmod) :
    ∃ W : WeierstrassCurve ℤ, W.IsIntegralModelOf E ∧ W.IsGoodPrimeFor ℓ ∧
      W.apOfModel ℓ = E.LFunction ℓ := by
  let v : HeightOneSpectrum (𝓞 ℚ) := Rat.HeightOneSpectrum.primesEquiv.symm ⟨ℓ, hℓ⟩
  have hv : (Rat.HeightOneSpectrum.primesEquiv v).val = ℓ :=
    congrArg Subtype.val (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply ⟨ℓ, hℓ⟩)
  have hNv : ¬ (Rat.HeightOneSpectrum.primesEquiv v).val ∣ modularConductor E hmod := by
    simpa only [hv] using hN
  simpa only [hv] using IntegralModelTransferAux.solution E hmod v hNv

end HorizontalPadicL

end publicSection
