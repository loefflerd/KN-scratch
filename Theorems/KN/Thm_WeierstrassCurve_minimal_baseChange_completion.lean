module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FinCases

section privateSection

-- Rational approximation will descend completed changes of variables.

open IsDedekindDomain NumberField Filter Topology

namespace MinimalCompletionAux

abbrev Parameters (K : Type*) := K × K × K × K

def parameterMap {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (x : Parameters K) : Parameters L :=
  (f x.1, f x.2.1, f x.2.2.1, f x.2.2.2)

def rawChange {K : Type*} [Field K] (W : WeierstrassCurve K)
    (x : Parameters K) : WeierstrassCurve K where
  a₁ := x.1⁻¹ * (W.a₁ + 2 * x.2.2.1)
  a₂ := x.1⁻¹ ^ 2 * (W.a₂ - x.2.2.1 * W.a₁ + 3 * x.2.1 - x.2.2.1 ^ 2)
  a₃ := x.1⁻¹ ^ 3 * (W.a₃ + x.2.1 * W.a₁ + 2 * x.2.2.2)
  a₄ := x.1⁻¹ ^ 4 * (W.a₄ - x.2.2.1 * W.a₃ + 2 * x.2.1 * W.a₂ -
    (x.2.2.2 + x.2.1 * x.2.2.1) * W.a₁ + 3 * x.2.1 ^ 2 - 2 * x.2.2.1 * x.2.2.2)
  a₆ := x.1⁻¹ ^ 6 * (W.a₆ + x.2.1 * W.a₄ + x.2.1 ^ 2 * W.a₂ + x.2.1 ^ 3 -
    x.2.2.2 * W.a₃ - x.2.2.2 ^ 2 - x.2.1 * x.2.2.2 * W.a₁)

def coefficients {K : Type*} (W : WeierstrassCurve K) : Fin 5 → K :=
  ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]

lemma rawChange_eq {K : Type*} [Field K] (W : WeierstrassCurve K)
    (x : Parameters K) (hx : x.1 ≠ 0) :
    rawChange W x = (⟨Units.mk0 x.1 hx, x.2.1, x.2.2.1, x.2.2.2⟩ :
      WeierstrassCurve.VariableChange K) • W := by
  rfl

lemma continuousAt_coefficients {K : Type*} [Field K] [TopologicalSpace K]
    [IsTopologicalDivisionRing K] (W : WeierstrassCurve K)
    (x : Parameters K) (hx : x.1 ≠ 0) (i : Fin 5) :
    ContinuousAt (fun y => coefficients (rawChange W y) i) x := by
  fin_cases i <;> simp only [coefficients, rawChange]
  all_goals fun_prop (disch := assumption)

lemma coefficients_integer {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (W : WeierstrassCurve K) [W.IsIntegral v.valuationSubring] :
    ∀ i, coefficients W i ∈ v.integer := by
  have heq := WeierstrassCurve.baseChange_integralModel_eq v.valuationSubring W
  rw [← heq]
  intro i
  fin_cases i <;> simp only [coefficients,
    WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  all_goals first
    | exact (WeierstrassCurve.integralModel v.valuationSubring W).a₁.property
    | exact (WeierstrassCurve.integralModel v.valuationSubring W).a₂.property
    | exact (WeierstrassCurve.integralModel v.valuationSubring W).a₃.property
    | exact (WeierstrassCurve.integralModel v.valuationSubring W).a₄.property
    | exact (WeierstrassCurve.integralModel v.valuationSubring W).a₆.property

/-- A completed integral change can be approximated by a rational change while keeping
the valuation of the scaling parameter exactly unchanged. -/
lemma descend_integral_change (v : HeightOneSpectrum (𝓞 ℚ))
    (E : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange (v.adicCompletion ℚ))
    [hC : (C • E.baseChange (v.adicCompletion ℚ)).IsIntegral
      (v.adicCompletionIntegers ℚ)] :
    ∃ D : WeierstrassCurve.VariableChange ℚ,
      (D.baseChange (v.adicCompletion ℚ) • E.baseChange (v.adicCompletion ℚ)).IsIntegral
        (v.adicCompletionIntegers ℚ) ∧
      Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (D.u : ℚ)) =
        Valued.v (C.u : v.adicCompletion ℚ) := by
  classical
  let K := v.adicCompletion ℚ
  let : (C • E.baseChange K).IsIntegral (v.adicCompletionIntegers ℚ) := hC
  let : (C • E.baseChange K).IsIntegral
      (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).valuationSubring := by
    exact hC
  let f := algebraMap ℚ K
  let x : Parameters K := (C.u, C.r, C.s, C.t)
  have hx : x.1 ≠ 0 := C.u.ne_zero
  have hraw : rawChange (E.baseChange K) x = C • E.baseChange K := by
    rw [rawChange_eq _ x hx]
    congr 1
    ext <;> rfl
  have hc : ∀ i, coefficients (rawChange (E.baseChange K) x) i ∈
      (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).integer := by
    rw [hraw]
    exact coefficients_integer Valued.v _
  have hn : ∀ i : Fin 5, ∀ᶠ y in 𝓝 x,
      coefficients (rawChange (E.baseChange K) y) i ∈
        (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).integer := by
    intro i
    exact (continuousAt_coefficients _ x hx i).preimage_mem_nhds
      ((Valued.isOpen_integer K).mem_nhds (hc i))
  have hu : ∀ᶠ y in 𝓝 x,
      (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).restrict y.1 =
        (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).restrict x.1 := by
    change {y : Parameters K | Valued.v.restrict y.1 = Valued.v.restrict x.1} ∈ 𝓝 x
    have hnonzero : Valued.v.restrict x.1 ≠ 0 := by
      apply mt (Valuation.restrict_eq_zero_iff
        (Valued.v : Valuation K (WithZero (Multiplicative ℤ)))).mp
      exact (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).ne_zero_iff.mpr hx
    exact ContinuousAt.preimage_mem_nhds
      (f := Prod.fst) (x := x) continuous_fst.continuousAt
      ((Valued.isOpen_sphere K hnonzero).mem_nhds rfl)
  have hd : DenseRange (parameterMap f) :=
    (v.denseRange_algebraMap (K := ℚ)).prodMap
      ((v.denseRange_algebraMap (K := ℚ)).prodMap
        ((v.denseRange_algebraMap (K := ℚ)).prodMap
          (v.denseRange_algebraMap (K := ℚ))))
  have hnear := (Filter.eventually_all.mpr hn).and hu
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hnear
  obtain ⟨z, hzU⟩ := hd.exists_mem_open hUopen ⟨x, hxU⟩
  obtain ⟨hzcoeff, hzu⟩ := hUsub hzU
  have hval : Valued.v (f z.1) = Valued.v x.1 :=
    (Valuation.restrict_inj (Valued.v : Valuation K (WithZero (Multiplicative ℤ)))).mp hzu
  have hz : z.1 ≠ 0 := by
    intro hz
    have hzero : Valued.v x.1 = 0 := by simpa [hz] using hval.symm
    exact hx ((Valued.v : Valuation K (WithZero (Multiplicative ℤ))).zero_iff.mp hzero)
  let D : WeierstrassCurve.VariableChange ℚ :=
    ⟨Units.mk0 z.1 hz, z.2.1, z.2.2.1, z.2.2.2⟩
  have hD : rawChange (E.baseChange K) (parameterMap f z) =
      D.baseChange K • E.baseChange K := by
    rw [rawChange_eq _ _ (by exact f.injective.ne hz)]
    congr 1
    ext <;> rfl
  refine ⟨D, ?_, hval⟩
  rw [← hD]
  apply WeierstrassCurve.isIntegral_of_exists_lift
  all_goals first
    | exact ⟨⟨_, hzcoeff 0⟩, rfl⟩
    | exact ⟨⟨_, hzcoeff 1⟩, rfl⟩
    | exact ⟨⟨_, hzcoeff 2⟩, rfl⟩
    | exact ⟨⟨_, hzcoeff 3⟩, rfl⟩
    | exact ⟨⟨_, hzcoeff 4⟩, rfl⟩

/-- Integrality is precisely membership of the five coefficients in the valuation ring. -/
lemma integral_iff_coefficients_mem {K : Type*} [Field K] (S : ValuationSubring K)
    (W : WeierstrassCurve K) : W.IsIntegral S ↔ ∀ i, coefficients W i ∈ S := by
  constructor
  · intro h
    let : W.IsIntegral S := h
    rw [← WeierstrassCurve.baseChange_integralModel_eq S W]
    intro i
    fin_cases i <;> simp only [coefficients, WeierstrassCurve.baseChange,
      WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
    all_goals first
      | exact (WeierstrassCurve.integralModel S W).a₁.property
      | exact (WeierstrassCurve.integralModel S W).a₂.property
      | exact (WeierstrassCurve.integralModel S W).a₃.property
      | exact (WeierstrassCurve.integralModel S W).a₄.property
      | exact (WeierstrassCurve.integralModel S W).a₆.property
  · intro h
    apply WeierstrassCurve.isIntegral_of_exists_lift S
    all_goals first
      | exact ⟨⟨_, h 0⟩, rfl⟩
      | exact ⟨⟨_, h 1⟩, rfl⟩
      | exact ⟨⟨_, h 2⟩, rfl⟩
      | exact ⟨⟨_, h 3⟩, rfl⟩
      | exact ⟨⟨_, h 4⟩, rfl⟩

lemma integral_baseChange_iff (v : HeightOneSpectrum (𝓞 ℚ)) (E : WeierstrassCurve ℚ) :
    (E.baseChange (v.adicCompletion ℚ)).IsIntegral (v.adicCompletionIntegers ℚ) ↔
      E.IsIntegral (v.valuationSubringAtPrime ℚ) := by
  rw [integral_iff_coefficients_mem, integral_iff_coefficients_mem]
  apply forall_congr'
  intro i
  have hi : coefficients (E.baseChange (v.adicCompletion ℚ)) i =
      algebraMap ℚ (v.adicCompletion ℚ) (coefficients E i) := by
    fin_cases i <;> rfl
  rw [hi, HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  rfl

/-- The normalized DVR valuation has the same ordering as any valuation with
the given DVR as its ring of integers. -/
lemma normalized_isEquiv {R K Γ : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) (hw : w.Integers R) :
    ((IsDiscreteValuationRing.maximalIdeal R).valuation K).IsEquiv w := by
  apply Valuation.isEquiv_of_val_le_one
  intro x
  constructor
  · intro hx
    obtain ⟨r, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K x (by
      intro q
      have hq : q = IsDiscreteValuationRing.maximalIdeal R :=
        HeightOneSpectrum.ext_iff.mpr (IsLocalRing.eq_maximalIdeal q.isMaximal)
      simpa [hq] using hx)
    exact hw.map_le_one r
  · intro hx
    obtain ⟨r, rfl⟩ := hw.exists_of_le_one hx
    exact HeightOneSpectrum.valuation_le_one _ r

end MinimalCompletionAux

open IsDedekindDomain NumberField

/-- The rational valuation subring at `v`: the localization of `𝓞 ℚ ≃ ℤ`,
not its completion. -/
noncomputable abbrev WeierstrassCurve.rationalLocalRing
    (v : HeightOneSpectrum (𝓞 ℚ)) := v.valuationSubringAtPrime ℚ

namespace WeierstrassCurve

local instance rationalLocalRing_isDiscreteValuationRing (v : HeightOneSpectrum (𝓞 ℚ)) :
    IsDiscreteValuationRing (v.valuationSubringAtPrime ℚ) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    (𝓞 ℚ) v.ne_bot (rationalLocalRing v)

/-- Minimal models can be chosen with rational coefficients, by minimizing over the
localization before completing. -/
theorem exists_minimal_over_rationalLocalRing (E : WeierstrassCurve ℚ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ C : VariableChange ℚ, IsMinimal (rationalLocalRing v) (C • E) :=
  E.exists_isMinimal (rationalLocalRing v)

/-- Minimizing over the rational localization already gives a minimal model over
the completed local field. -/
theorem isMinimal_baseChange_completion (E : WeierstrassCurve ℚ)
    (v : HeightOneSpectrum (𝓞 ℚ)) [E.IsMinimal (rationalLocalRing v)] :
    (E.baseChange (v.adicCompletion ℚ)).IsMinimal (v.adicCompletionIntegers ℚ) := by
  classical
  let R := rationalLocalRing v
  let K := v.adicCompletion ℚ
  let S := v.adicCompletionIntegers ℚ
  let w : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  have hwR : (v.valuation ℚ).Integers R := by
    refine ⟨Subtype.coe_injective, ?_, ?_⟩
    · intro r
      change (r : ℚ) ∈ (v.valuation ℚ).valuationSubring
      rw [← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      exact r.property
    · intro x hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      change x ∈ v.valuationSubringAtPrime ℚ
      rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      exact hx
  have eR := MinimalCompletionAux.normalized_isEquiv (v.valuation ℚ) hwR
  have eS := MinimalCompletionAux.normalized_isEquiv w
    (HeightOneSpectrum.adicCompletionIntegers.integers ℚ v)
  let : (E.baseChange K).IsIntegral S :=
    (MinimalCompletionAux.integral_baseChange_iff v E).mpr inferInstance
  have hv (a : ℚ) : w (algebraMap ℚ K a) = v.valuation ℚ a := by
    simp only [w, K, HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  constructor
  refine ⟨by simpa, ?_⟩
  intro C hC _
  let : (C • E.baseChange K).IsIntegral S := hC
  obtain ⟨D, hD, hu⟩ := MinimalCompletionAux.descend_integral_change v E C
  have hDmap : D.baseChange K • E.baseChange K = (D • E).baseChange K :=
    map_variableChange E D (algebraMap ℚ K)
  have hDR : (D • E).IsIntegral R :=
    (MinimalCompletionAux.integral_baseChange_iff v (D • E)).mp (hDmap ▸ hD)
  let : (D • E).IsIntegral R := hDR
  have hmax : valuation_Δ_aux R (D • E) ≤ valuation_Δ_aux R E := by
    have hm := (IsMinimal.val_Δ_maximal (R := R) (W := E))
    rcases le_total (valuation_Δ_aux R (D • E)) (valuation_Δ_aux R E) with h | h
    · exact h
    · simpa using hm.2 hDR (by simpa using h)
  have hnorm : (IsDiscreteValuationRing.maximalIdeal R).valuation ℚ (D • E).Δ ≤
      (IsDiscreteValuationRing.maximalIdeal R).valuation ℚ E.Δ := by
    have hcoe : (valuation_Δ_aux R (D • E) : WithZero (Multiplicative ℤ)) ≤
        (valuation_Δ_aux R E : WithZero (Multiplicative ℤ)) := hmax
    simpa only [valuation_Δ_aux_eq_of_isIntegral] using hcoe
  have hrat := (eR (D • E).Δ E.Δ).mp hnorm
  have hdelta : w (C • E.baseChange K).Δ = v.valuation ℚ (D • E).Δ := by
    calc
      w (C • E.baseChange K).Δ = w (D.baseChange K • E.baseChange K).Δ := by
        simp only [variableChange_Δ, map_mul, map_pow, Units.val_inv_eq_inv_val,
          map_inv₀]
        simpa only [VariableChange.baseChange, VariableChange.map, Units.coe_map,
          MonoidHom.coe_ofClass] using congrArg
            (fun a => a⁻¹ ^ 12 * w (E.baseChange K).Δ) hu.symm
      _ = v.valuation ℚ (D • E).Δ := by
        rw [hDmap]
        exact (congrArg w (map_Δ (D • E) (algebraMap ℚ K))).trans (hv _)
  have hcomp : w (C • E.baseChange K).Δ ≤ w (E.baseChange K).Δ := by
    rw [hdelta, show (E.baseChange K).Δ = algebraMap ℚ K E.Δ from map_Δ _ _, hv]
    exact hrat
  have hs := (eS (C • E.baseChange K).Δ (E.baseChange K).Δ).mpr hcomp
  change (valuation_Δ_aux S (C • E.baseChange K) : WithZero (Multiplicative ℤ)) ≤
    (valuation_Δ_aux S (1 • E.baseChange K) : WithZero (Multiplicative ℤ))
  simpa only [one_smul, valuation_Δ_aux_eq_of_isIntegral] using hs

end WeierstrassCurve

end privateSection

public section publicSection

open IsDedekindDomain NumberField

namespace WeierstrassCurve

/-- A single rational change gives a minimal model both before and after completion. -/
theorem exists_minimal_rational_model_and_completion (E : WeierstrassCurve ℚ)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    letI : IsDiscreteValuationRing (v.valuationSubringAtPrime ℚ) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
        (𝓞 ℚ) v.ne_bot (v.valuationSubringAtPrime ℚ)
    ∃ C : VariableChange ℚ,
      IsMinimal (v.valuationSubringAtPrime ℚ) (C • E) ∧
      IsMinimal (v.adicCompletionIntegers ℚ) ((C • E).baseChange (v.adicCompletion ℚ)) := by
  have : IsDiscreteValuationRing (rationalLocalRing v) :=
    rationalLocalRing_isDiscreteValuationRing v
  obtain ⟨C, hC⟩ := exists_minimal_over_rationalLocalRing E v
  have : IsMinimal (rationalLocalRing v) (C • E) := hC
  exact ⟨C, hC, isMinimal_baseChange_completion (C • E) v⟩

end WeierstrassCurve

end publicSection
