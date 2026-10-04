import Definitions.KN.Def_HorizontalPadicL_LocalEulerFactorDegree
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.RingHoms
import Definitions.KN.Def_KN_HorizontalPadicL
import Definitions.FLT.Def_FreyPackage_ModMCarrier_Rescale
import Definitions.FLT.Def_ModularForm_HeckeOperator
import Definitions.FLT.Def_FLTPrelim_Modularity
import Theorems.FLT.Thm_CongruenceSubgroup_Gamma0_le_closure_T_union_setOf_dvd
import Theorems.FLT.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.FLT.Thm_CuspForm_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero
import Theorems.MTT.Thm_MTT_hasSum_heckePrime
import Theorems.MTT.Thm_MTT_exists_cuspForm_heckePrime_pos

-- From Solutions/MinimalLevelArithmetic.lean
/-
The rational completion residue-field comparison is adapted from
Norwich/Preliminaries/LFunctionGoodReduction.lean.
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Authors of the adapted comparison: Riccardo Brasca.
Released under the Apache License, Version 2.0:
https://www.apache.org/licenses/LICENSE-2.0
The other arithmetic lemmas and the prime-power generalization are new here.
-/

noncomputable section
open scoped BigOperators

namespace ArithmeticFunction

lemma prod_apply_eq_of_eq_on_divisors {ι R : Type*} [CommSemiring R]
    (f g : ι → ArithmeticFunction R) (s : Finset ι) (n : ℕ)
    (h : ∀ i ∈ s, ∀ d, d ∣ n → f i d = g i d) :
    (∏ i ∈ s, f i) n = (∏ i ∈ s, g i) n := by
  classical
  induction s using Finset.induction generalizing n with
  | empty => rfl
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, mul_apply, mul_apply]
    apply Finset.sum_congr rfl
    intro d hd
    have hdn := Nat.mem_divisorsAntidiagonal.mp hd
    rw [h i (Finset.mem_insert_self i s) d.1 (Dvd.intro d.2 hdn.1), ih]
    intro j hj e he
    exact h j (Finset.mem_insert_of_mem hj) e
      (he.trans (Dvd.intro_left d.1 hdn.1))

open Filter in
lemma eulerProduct_ofPowerSeries_apply_prime_pow {ι R : Type*} [CommSemiring R]
    (q : ι → ℕ) [Northcott q] (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q)
    (f : ι → PowerSeries R) (hf : ∀ i, (f i).constantCoeff = 1) (i₀ : ι) (r : ℕ) :
    eulerProduct (fun i ↦ ofPowerSeries (q i) (f i)) ((q i₀) ^ r) = (f i₀).coeff r := by
  classical
  let g : ι → ArithmeticFunction R := fun i ↦ ofPowerSeries (q i) (f i)
  have hunit : ∀ i, i ≠ i₀ → ∀ d, d ∣ (q i₀) ^ r → g i d = (1 : ArithmeticFunction R) d := by
    intro i hi d hd
    by_cases hd1 : d = 1
    · simp [hd1, g, hf]
    rw [one_apply_ne hd1, ofPowerSeries_apply (hq i).one_lt]
    apply Function.extend_apply'
    rintro ⟨k, hk⟩
    have hk0 : k ≠ 0 := by rintro rfl; simp_all
    have hdiv : q i ∣ q i₀ := (hq i).dvd_of_dvd_pow
      ((dvd_pow_self _ hk0).trans (hk ▸ hd))
    exact hi (hinj ((Nat.prime_dvd_prime_iff_eq (hq i) (hq i₀)).mp hdiv))
  have htend := tendsTo_eulerProduct_ofPowerSeries q f hf ((q i₀) ^ r)
  rw [eventually_atTop] at htend
  obtain ⟨s, hs⟩ := htend
  rw [← hs (insert i₀ s) (Finset.subset_insert i₀ s)]
  change (∏ i ∈ insert i₀ s, g i) ((q i₀) ^ r) = _
  rw [prod_apply_eq_of_eq_on_divisors g
    (fun i ↦ if i = i₀ then g i₀ else 1) (insert i₀ s) ((q i₀) ^ r) (by
      intro i hi d hd
      by_cases hii : i = i₀
      · simp [hii]
      · simpa [hii] using hunit i hii d hd)]
  rw [Finset.prod_eq_single i₀ (by intros; simp_all) (by simp), ite_eq_left rfl]
  exact ofPowerSeries_apply_pow (hq i₀).one_lt (f i₀) r

lemma IsMultiplicative.prime_mul_recurrence {R : Type*} [CommRing R]
    {f : ArithmeticFunction R} (hf : f.IsMultiplicative) {p : ℕ} (hp : p.Prime)
    (b : R) (hrec : ∀ r : ℕ, f (p ^ (r + 2)) =
      f p * f (p ^ (r + 1)) - b * f (p ^ r)) (n : ℕ) :
    f (p * n) = f p * f n - if p ∣ n then b * f (n / p) else 0 := by
  classical
  by_cases hn : n = 0
  · simp [hn]
  obtain ⟨r, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have hpu : Nat.Coprime p u := hp.coprime_iff_not_dvd.mpr hu
  cases r with
  | zero => simpa [hu] using hf.2 hpu
  | succ r =>
    have hd : p ∣ p ^ (r + 1) * u := dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) _
    have hdiv : p ^ (r + 1) * u / p = p ^ r * u := by
      rw [pow_succ', Nat.mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
    have hmul : p * (p ^ (r + 1) * u) = p ^ (r + 2) * u := by
      rw [← Nat.mul_assoc, ← pow_succ']
    rw [ite_eq_left hd, hdiv, hmul, hf.2 (hpu.pow_left (r + 2)),
      hf.2 (hpu.pow_left (r + 1)), hf.2 (hpu.pow_left r), hrec]
    ring

end ArithmeticFunction

namespace PowerSeries

lemma coeff_invOfUnit_quadratic_recurrence (a b : ℤ) (r : ℕ) :
    let s := invOfUnit (1 - C a * X + C b * X ^ 2 : PowerSeries ℤ) 1
    s.coeff (r + 2) = a * s.coeff (r + 1) - b * s.coeff r := by
  intro s
  have h := mul_invOfUnit (1 - C a * X + C b * X ^ 2 : PowerSeries ℤ) 1 (by simp)
  have heq : s - C a * s * X + C b * s * X ^ 2 = 1 := by
    dsimp [s]
    convert h using 1
    ring
  have hc := congrArg (coeff (r + 2)) heq
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_succ_mul_X, coeff_C_mul,
    coeff_one] at hc
  simp at hc
  omega

lemma coeff_one_invOfUnit_quadratic (a b : ℤ) :
    (invOfUnit (1 - C a * X + C b * X ^ 2 : PowerSeries ℤ) 1).coeff 1 = a := by
  let s := invOfUnit (1 - C a * X + C b * X ^ 2 : PowerSeries ℤ) 1
  have h := mul_invOfUnit (1 - C a * X + C b * X ^ 2 : PowerSeries ℤ) 1 (by simp)
  have heq : s - C a * s * X + C b * s * X ^ 2 = 1 := by
    dsimp [s]
    convert h using 1
    ring
  have hc := congrArg (coeff 1) heq
  simp [coeff_mul_X_pow', coeff_succ_mul_X, s,
    coeff_zero_eq_constantCoeff] at hc
  simpa using sub_eq_zero.mp hc

end PowerSeries

namespace WeierstrassCurve

lemma localPolynomial_exists_quadratic
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (E : WeierstrassCurve K) :
    ∃ a b : ℤ, (b = 0 ∨ b = Nat.card (IsLocalRing.ResidueField R)) ∧
      E.localPolynomial R = 1 - Polynomial.C a * Polynomial.X +
        Polynomial.C b * Polynomial.X ^ 2 := by
  classical
  unfold localPolynomial
  split_ifs
  · exact ⟨_, _, Or.inr rfl, rfl⟩
  · refine ⟨1, 0, Or.inl rfl, ?_⟩
    simp
  · refine ⟨-1, 0, Or.inl rfl, ?_⟩
    simp
  · refine ⟨0, 0, Or.inl rfl, ?_⟩
    simp

lemma localPowerSeries_recurrence
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (E : WeierstrassCurve K) :
    ∃ b : ℤ, (b = 0 ∨ b = Nat.card (IsLocalRing.ResidueField R)) ∧
      ∀ r : ℕ, (E.localPowerSeries R).coeff (r + 2) =
        (E.localPowerSeries R).coeff 1 * (E.localPowerSeries R).coeff (r + 1) -
          b * (E.localPowerSeries R).coeff r := by
  obtain ⟨a, b, hb, hab⟩ := E.localPolynomial_exists_quadratic R
  refine ⟨b, hb, fun r ↦ ?_⟩
  unfold localPowerSeries
  rw [hab]
  simp only [Polynomial.coe_add, Polynomial.coe_sub, Polynomial.coe_one,
    Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X, Polynomial.coe_pow]
  rw [PowerSeries.coeff_one_invOfUnit_quadratic]
  exact PowerSeries.coeff_invOfUnit_quadratic_recurrence a b r

lemma localPowerSeries_constantCoeff
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (E : WeierstrassCurve K) :
    (E.localPowerSeries R).constantCoeff = 1 := by
  simp [localPowerSeries, PowerSeries.constantCoeff_invOfUnit]

lemma localEulerFactor_isMultiplicative
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (E : WeierstrassCurve K) :
    E.localEulerFactor R |>.IsMultiplicative := by
  classical
  cases finite_or_infinite (IsLocalRing.ResidueField R)
  · let := Fintype.ofFinite (IsLocalRing.ResidueField R)
    apply ArithmeticFunction.isMultiplicative_ofPowerSeries_of_isPrimePow
    · rw [Nat.card_eq_fintype_card]
      exact FiniteField.isPrimePow_card _
    · exact E.localPowerSeries_constantCoeff R
  · unfold localEulerFactor
    rw [Nat.card_eq_zero_of_infinite]
    have h : (E.localPowerSeries R).constantCoeff = 1 := E.localPowerSeries_constantCoeff R
    simp [ArithmeticFunction.ofPowerSeries, h, ArithmeticFunction.isMultiplicative_one]

lemma LFunction_isMultiplicative
    {K : Type*} [Field K] [NumberField K] (E : WeierstrassCurve K) :
    E.LFunction.IsMultiplicative := by
  apply ArithmeticFunction.isMultiplicative_eulerProduct
  intro p
  exact (E.baseChange (p.adicCompletion K)).localEulerFactor_isMultiplicative _

@[simp] lemma LFunction_one
    {K : Type*} [Field K] [NumberField K] (E : WeierstrassCurve K) : E.LFunction 1 = 1 :=
  E.LFunction_isMultiplicative.1

lemma LFunction_mul_of_coprime
    {K : Type*} [Field K] [NumberField K] (E : WeierstrassCurve K)
    {a b : ℕ} (hab : Nat.Coprime a b) : E.LFunction (a * b) = E.LFunction a * E.LFunction b :=
  E.LFunction_isMultiplicative.2 hab

/-- The rational completion has the same residue cardinality as its corresponding prime.
This proof follows Riccardo Brasca's `Norwich/Preliminaries/LFunctionGoodReduction.lean`. -/
lemma rat_completion_residueCard
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) =
      (Rat.HeightOneSpectrum.primesEquiv v : ℕ) := by
  have : Fact (Rat.HeightOneSpectrum.primesEquiv v).1.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  let e := (IsLocalRing.ResidueField.mapEquiv
    (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toRingEquiv).trans
      PadicInt.residueField
  rw [Nat.card_congr e.toEquiv, Nat.card_zmod]

lemma LFunction_prime_pow_eq_localPowerSeries (E : WeierstrassCurve ℚ)
    {p : ℕ} (hp : p.Prime) (r : ℕ) :
    let v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) :=
      Rat.HeightOneSpectrum.primesEquiv.symm (⟨p, hp⟩ : Nat.Primes)
    E.LFunction (p ^ r) = ((E.baseChange (v.adicCompletion ℚ)).localPowerSeries
      (v.adicCompletionIntegers ℚ)).coeff r := by
  intro v
  let q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) → ℕ :=
    fun w ↦ Rat.HeightOneSpectrum.primesEquiv w
  have hqinj : Function.Injective q :=
    fun i j h ↦ Rat.HeightOneSpectrum.primesEquiv.injective (Subtype.val_injective h)
  have : Northcott q := ⟨fun b ↦ (Set.finite_Iic b).preimage hqinj.injOn⟩
  have hq (w) : (q w).Prime := (Rat.HeightOneSpectrum.primesEquiv w).2
  have hqv : q v = p := congrArg Subtype.val
    ((Rat.HeightOneSpectrum.primesEquiv
      (R := NumberField.RingOfIntegers ℚ)).apply_symm_apply ⟨p, hp⟩)
  unfold LFunction localEulerFactor
  simp_rw [rat_completion_residueCard]
  rw [← hqv]
  apply ArithmeticFunction.eulerProduct_ofPowerSeries_apply_prime_pow q hq hqinj
  intro w
  exact (E.baseChange (w.adicCompletion ℚ)).localPowerSeries_constantCoeff _

end WeierstrassCurve

namespace HorizontalPadicL

/-- Every elliptic Euler polynomial over the rationals is linear or has the
weight-two quadratic term, expressed through its reciprocal coefficients. -/
lemma localEulerFactorDegree_dichotomy (E : WeierstrassCurve ℚ) {p : ℕ} (hp : p.Prime) :
    LocalEulerFactorDegreeBelowTwo E p ∨ LocalEulerFactorDegreeTwo E p := by
  let v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) :=
    Rat.HeightOneSpectrum.primesEquiv.symm ⟨p, hp⟩
  obtain ⟨b, hb, hrec⟩ :=
    (E.baseChange (v.adicCompletion ℚ)).localPowerSeries_recurrence (v.adicCompletionIntegers ℚ)
  have hcard : Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) = p := by
    rw [WeierstrassCurve.rat_completion_residueCard]
    exact congrArg Subtype.val
      ((Rat.HeightOneSpectrum.primesEquiv
      (R := NumberField.RingOfIntegers ℚ)).apply_symm_apply ⟨p, hp⟩)
  rw [hcard] at hb
  have hcoeff (r : ℕ) : ((E.baseChange (v.adicCompletion ℚ)).localPowerSeries
      (v.adicCompletionIntegers ℚ)).coeff r = E.LFunction (p ^ r) :=
    (E.LFunction_prime_pow_eq_localPowerSeries hp r).symm
  simp_rw [hcoeff, pow_one] at hrec
  rcases hb with rfl | rfl
  · left
    simpa [LocalEulerFactorDegreeBelowTwo] using hrec
  · exact Or.inr hrec

lemma LocalEulerFactorDegreeBelowTwo.LFunction_prime_mul
    {E : WeierstrassCurve ℚ} {p : ℕ} (h : LocalEulerFactorDegreeBelowTwo E p)
    (hp : p.Prime) (n : ℕ) : E.LFunction (p * n) = E.LFunction p * E.LFunction n := by
  have hrec : ∀ r : ℕ, E.LFunction (p ^ (r + 2)) =
      E.LFunction p * E.LFunction (p ^ (r + 1)) - (0 : ℤ) * E.LFunction (p ^ r) := by
    simpa [LocalEulerFactorDegreeBelowTwo] using h
  simpa using E.LFunction_isMultiplicative.prime_mul_recurrence hp 0 hrec n

lemma LocalEulerFactorDegreeTwo.LFunction_prime_mul
    {E : WeierstrassCurve ℚ} {p : ℕ} (h : LocalEulerFactorDegreeTwo E p)
    (hp : p.Prime) (n : ℕ) :
    E.LFunction (p * n) = E.LFunction p * E.LFunction n -
      if p ∣ n then (p : ℤ) * E.LFunction (n / p) else 0 :=
  E.LFunction_isMultiplicative.prime_mul_recurrence hp p h n

lemma ModularFormAtLevel.qExpansion_coeff_one
    {E : WeierstrassCurve ℚ} {N : ℕ} (f : ModularFormAtLevel E N) :
    (UpperHalfPlane.qExpansion 1 f.form).coeff 1 = 1 := by
  rw [← f.coeff_eq, E.LFunction_one, Int.cast_one]

lemma localEulerFactorDegree_not_both (E : WeierstrassCurve ℚ) {p : ℕ} (hp : p.Prime) :
    ¬ (LocalEulerFactorDegreeBelowTwo E p ∧ LocalEulerFactorDegreeTwo E p) := by
  intro ⟨hlin, hquad⟩
  have hlin0 := hlin 0
  have hquad0 := hquad 0
  simp only [zero_add, pow_one, pow_zero, E.LFunction_one, mul_one] at hlin0 hquad0
  have hpzero : (p : ℤ) = 0 := by omega
  exact hp.ne_zero (Int.ofNat_eq_zero.mp hpzero)

end HorizontalPadicL

end

-- From Solutions/MinimalLevelDescent.lean
/-
The auxiliary inverse-slash descent construction is adapted from
anthropics/fermats-last-theorem,
P2M/Sol/S_CuspForm_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero.lean.
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0:
https://www.apache.org/licenses/LICENSE-2.0
The normalization and combined descent theorem at the end are new here.
-/

/-!
Prime-support descent, following Atkin–Lehner (1970), Lemma 16.
The auxiliary descent construction is adapted from the completed Prove2Me
solution `S_CuspForm_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero`.
-/

noncomputable section

open UpperHalfPlane ModularForm OnePoint Function
open scoped MatrixGroups ModularForm Topology

namespace HorizontalPadicL.MinimalLevelDescentAux

theorem qParam_vadd_pow {q n : ℕ} (hq : q ≠ 0) (hn : q ∣ n) (τ : ℍ) :
    Periodic.qParam 1 ((((q : ℝ)⁻¹ +ᵥ τ : ℍ) : ℂ)) ^ n = Periodic.qParam 1 (τ : ℂ) ^ n := by
  obtain ⟨k, rfl⟩ := hn
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  unfold Periodic.qParam
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, UpperHalfPlane.coe_vadd]
  push_cast
  have hqq : (q : ℂ) * (q : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hq'
  rw [show (q : ℂ) * (k : ℂ) * (2 * Real.pi * Complex.I * (((q : ℂ))⁻¹ + (τ : ℂ)) / 1)
      = (q : ℂ) * (k : ℂ) * (2 * Real.pi * Complex.I * (τ : ℂ) / 1) + (k : ℂ) * (2 * Real.pi * Complex.I)
      by linear_combination ((k : ℂ) * (2 * Real.pi * Complex.I)) * hqq,
    Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

theorem apply_vadd_eq {m q : ℕ} [NeZero m] (hq : q ≠ 0)
    (F : CuspForm (CongruenceSubgroup.Gamma0 m) 2)
    (hF : ∀ n : ℕ, ¬ q ∣ n → ModularFormClass.qCoeff F n = 0) (τ : ℍ) :
    F ((q : ℝ)⁻¹ +ᵥ τ) = F τ := by
  have hper : Periodic (⇑F ∘ ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex F (by simp)
  have h1 := UpperHalfPlane.hasSum_qExpansion one_pos hper (CuspFormClass.holo F)
    (ModularFormClass.bdd_at_infty F) τ
  have h2 := UpperHalfPlane.hasSum_qExpansion one_pos hper (CuspFormClass.holo F)
    (ModularFormClass.bdd_at_infty F) ((q : ℝ)⁻¹ +ᵥ τ)
  have hfun : (fun n : ℕ => (qExpansion 1 ⇑F).coeff n • Periodic.qParam 1
        ((((q : ℝ)⁻¹ +ᵥ τ : ℍ) : ℂ)) ^ n)
      = fun n : ℕ => (qExpansion 1 ⇑F).coeff n • Periodic.qParam 1 (τ : ℂ) ^ n := by
    funext n
    by_cases hn : q ∣ n
    · rw [qParam_vadd_pow hq hn]
    · have h0 : (qExpansion 1 ⇑F).coeff n = 0 := hF n hn
      rw [h0, zero_smul, zero_smul]
  rw [hfun] at h2
  exact h2.unique h1

abbrev B (q : ℕ) : GL (Fin 2) ℝ := heckeDiagMatrix q

def Tq (q : ℕ) : GL (Fin 2) ℝ :=
  upperTriangularGL 1 ((q : ℝ)⁻¹) 1 (by norm_num)

theorem T_mul_B {q : ℕ} (hq : q ≠ 0) :
    (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) * B q = B q * Tq q := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  change ((ModularGroup.T : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) *
      ((heckeDiagMatrix q : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
    = ((heckeDiagMatrix q : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
      ((Tq q : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
  rw [val_heckeDiagMatrix hq, ModularGroup.coe_T, Tq, val_upperTriangularGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hq']

theorem Binv_mul_T {q : ℕ} (hq : q ≠ 0) :
    (B q)⁻¹ * (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ)
      = Tq q * (B q)⁻¹ := by
  rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← T_mul_B hq, mul_assoc, mul_inv_cancel, mul_one]

theorem slash_Tq_apply {q : ℕ} (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[(2 : ℤ)] Tq q) τ = f ((q : ℝ)⁻¹ +ᵥ τ) := by
  have hdet : ((Tq q).det : ℝ) = 1 := by
    simp [Tq, Matrix.det_fin_two_of]
  have hdetpos : 0 < ((Tq q).det : ℝ) := by rw [hdet]; exact one_pos
  have hσ : UpperHalfPlane.σ (Tq q) = .refl ℝ ℂ := by
    rw [UpperHalfPlane.σ, ite_eq_left hdetpos]
  have hdenom : UpperHalfPlane.denom (Tq q) τ = 1 := by
    simp [UpperHalfPlane.denom, Tq]
  have hsmul : (Tq q • τ : ℍ) = (q : ℝ)⁻¹ +ᵥ τ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos hdetpos, UpperHalfPlane.coe_vadd, hdenom, div_one]
    simp [UpperHalfPlane.num, Tq, add_comm]
  rw [ModularForm.slash_apply, hσ, hdet, hdenom, hsmul]
  simp

theorem exists_inv_cocycle {q R : ℕ} {γ : SL(2, ℤ)}
    (hc : (R : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
    (hb : (q : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1) :
    ∃ γ' : SL(2, ℤ), γ' ∈ CongruenceSubgroup.Gamma0 (q * R) ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ) * FreyPackage.ModMCarrier.diagMatInt q
        = FreyPackage.ModMCarrier.diagMatInt q * (γ' : Matrix (Fin 2) (Fin 2) ℤ) := by
  have hdet : (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  set a : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with ha
  set b : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hb'
  set c : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hc'
  set e : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with he
  have hγmat : (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; c, e] := by
    rw [ha, hb', hc', he]; exact Matrix.eta_fin_two _
  obtain ⟨b₁, hb₁⟩ := hb
  obtain ⟨c₁, hc₁⟩ := hc
  have hdetδ : Matrix.det !![a, b₁; c * (q : ℤ), e] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination hdet + c * hb₁
  refine ⟨⟨_, hdetδ⟩, ?_, ?_⟩
  · change ((c * (q : ℤ) : ℤ) : ZMod (q * R)) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hc₁]
    exact ⟨c₁, by push_cast; ring⟩
  · show (γ : Matrix (Fin 2) (Fin 2) ℤ) * FreyPackage.ModMCarrier.diagMatInt q
      = FreyPackage.ModMCarrier.diagMatInt q * !![a, b₁; c * (q : ℤ), e]
    rw [hγmat]; unfold FreyPackage.ModMCarrier.diagMatInt
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j
    · show (a * (q : ℤ) + b * 0 : ℤ) = (q : ℤ) * a + 0 * (c * (q : ℤ)); ring
    · show (a * 0 + b * 1 : ℤ) = (q : ℤ) * b₁ + 0 * e; linear_combination hb₁
    · show (c * (q : ℤ) + e * 0 : ℤ) = 0 * a + 1 * (c * (q : ℤ)); ring
    · show (c * 0 + e * 1 : ℤ) = 0 * b₁ + 1 * e; ring

theorem map_int_mul_eq (A C : Matrix (Fin 2) (Fin 2) ℤ) :
    (A * C).map (algebraMap ℤ ℝ) = A.map (algebraMap ℤ ℝ) * C.map (algebraMap ℤ ℝ) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_mul]

theorem Binv_mul_mapGL {q R : ℕ} (hq : q ≠ 0) {γ : SL(2, ℤ)}
    (hc : (R : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
    (hb : (q : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1) :
    ∃ γ' : SL(2, ℤ), γ' ∈ CongruenceSubgroup.Gamma0 (q * R) ∧
      (B q)⁻¹ * (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)
        = (Matrix.SpecialLinearGroup.mapGL ℝ γ' : GL (Fin 2) ℝ) * (B q)⁻¹ := by
  obtain ⟨γ', hγ', hconj⟩ := exists_inv_cocycle hc hb
  refine ⟨γ', hγ', ?_⟩
  have hGL : (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) * B q
      = B q * (Matrix.SpecialLinearGroup.mapGL ℝ γ' : GL (Fin 2) ℝ) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    change ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) *
        ((heckeDiagMatrix q : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = ((heckeDiagMatrix q : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
        ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ)
    rw [← FreyPackage.ModMCarrier.diagMatInt_map_eq hq, ← map_int_mul_eq, ← map_int_mul_eq, hconj]
  rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hGL, mul_assoc, mul_inv_cancel, mul_one]

def stab (f : ℍ → ℂ) (k : ℤ) : Subgroup SL(2, ℤ) where
  carrier := {g | f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) = f}
  one_mem' := by
    show f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (1 : SL(2, ℤ)) : GL (Fin 2) ℝ) = f
    rw [map_one, SlashAction.slash_one]
  mul_mem' := by
    intro a b ha hb
    show f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (a * b) : GL (Fin 2) ℝ) = f
    rw [map_mul, SlashAction.slash_mul, ha, hb]
  inv_mem' := by
    intro a ha
    show f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ a⁻¹ : GL (Fin 2) ℝ) = f
    calc f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ a⁻¹ : GL (Fin 2) ℝ)
        = (f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ a : GL (Fin 2) ℝ)) ∣[k]
            (Matrix.SpecialLinearGroup.mapGL ℝ a⁻¹ : GL (Fin 2) ℝ) := by rw [ha]
      _ = f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ a : GL (Fin 2) ℝ) *
            (Matrix.SpecialLinearGroup.mapGL ℝ a⁻¹ : GL (Fin 2) ℝ)) :=
          (SlashAction.slash_mul k _ _ f).symm
      _ = f := by rw [← map_mul, mul_inv_cancel, map_one, SlashAction.slash_one]

theorem mem_stab_iff (f : ℍ → ℂ) (k : ℤ) (g : SL(2, ℤ)) :
    g ∈ stab f k ↔ f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) = f := Iff.rfl

theorem isCusp_smul_of_rat {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) {g : GL (Fin 2) ℝ}
    (gQ : GL (Fin 2) ℚ) (hg : gQ.map (Rat.castHom ℝ) = g) : IsCusp (g • c) 𝒮ℒ := by
  subst hg
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c₀, rfl⟩ := hc
  exact ⟨gQ • c₀, by rw [← Rat.coe_castHom, OnePoint.map_smul]⟩

section build

variable {m q R : ℕ} [NeZero m] [NeZero R]

def descend (hq : q ≠ 0) (hmR : m ∣ q * R) (F : CuspForm (CongruenceSubgroup.Gamma0 m) 2)
    (hF : ∀ n : ℕ, ¬ q ∣ n → ModularFormClass.qCoeff F n = 0) :
    CuspForm (CongruenceSubgroup.Gamma0 R) 2 :=
  { toFun := ⇑F ∣[(2 : ℤ)] (B q)⁻¹
    slash_action_eq' := fun γ hγ => by
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
      have hgen : Subgroup.closure ({ModularGroup.T} ∪ {γ : SL(2, ℤ) |
            (R : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ∧
            (q : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1})
          ≤ stab (⇑F ∣[(2 : ℤ)] (B q)⁻¹) 2 := by
        rw [Subgroup.closure_le]
        rintro g (hT | ⟨hgc, hgb⟩)
        · rw [Set.mem_singleton_iff] at hT
          subst hT
          rw [SetLike.mem_coe, mem_stab_iff, ← SlashAction.slash_mul, Binv_mul_T hq,
            SlashAction.slash_mul]
          congr 1
          funext τ
          rw [slash_Tq_apply]
          exact apply_vadd_eq hq F hF τ
        · obtain ⟨g', hg', hconj⟩ := Binv_mul_mapGL (R := R) hq hgc hgb
          rw [SetLike.mem_coe, mem_stab_iff, ← SlashAction.slash_mul, hconj,
            SlashAction.slash_mul]
          congr 1
          have hg'm : g' ∈ CongruenceSubgroup.Gamma0 m := by
            rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hg' ⊢
            exact (Int.natCast_dvd_natCast.mpr hmR).trans (by exact_mod_cast hg')
          exact SlashInvariantFormClass.slash_action_eq F _
            (Subgroup.mem_map.mpr ⟨g', hg'm, rfl⟩)
      have hle := (CongruenceSubgroup.Gamma0_le_closure_T_union_setOf_dvd R hq).trans hgen
      exact (mem_stab_iff _ _ _).mp (hle hg)
    holo' := (CuspFormClass.holo F).slash (2 : ℤ) (B q)⁻¹
    zero_at_cusps' := fun {c} hc => by
      refine IsZeroAt.smul_iff.mp (CuspFormClass.zero_at_cusps F ?_)
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
      exact isCusp_smul_of_rat hc (FreyPackage.ModMCarrier.heckeDiagMatrixQ hq)⁻¹
        (by rw [map_inv, FreyPackage.ModMCarrier.heckeDiagMatrixQ_map]) }

theorem coe_descend (hq : q ≠ 0) (hmR : m ∣ q * R) (F : CuspForm (CongruenceSubgroup.Gamma0 m) 2)
    (hF : ∀ n : ℕ, ¬ q ∣ n → ModularFormClass.qCoeff F n = 0) :
    ⇑(descend hq hmR F hF) = ⇑F ∣[(2 : ℤ)] (B q)⁻¹ := rfl

end build

end HorizontalPadicL.MinimalLevelDescentAux

open HorizontalPadicL.MinimalLevelDescentAux in
theorem CuspForm.exists_qExpansion_descent_of_prime_support
    {N p : ℕ} (hN : 0 < N) (hp : p.Prime)
    (g : HorizontalPadicL.CuspFormAtLevel N hN)
    (hg : (qExpansion 1 g).coeff p ≠ 0)
    (hsupp : ∀ n : ℕ, ¬ p ∣ n → (qExpansion 1 g).coeff n = 0) :
    p ∣ N ∧ ∃ hM : 0 < N / p,
      ∃ f : HorizontalPadicL.CuspFormAtLevel (N / p) hM,
        ∀ n : ℕ, (qExpansion 1 f).coeff n = (qExpansion 1 g).coeff (p * n) := by
  let : NeZero N := ⟨hN.ne'⟩
  have hsupp' : ∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff g n = 0 := hsupp
  have hpN : p ∣ N := by
    by_contra hnot
    have hz := CuspForm.eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero hp hnot g hsupp'
    apply hg
    rw [hz]
    simp only [FunLike.coe_zero, qExpansion_zero, map_zero]
  have hM : 0 < N / p := Nat.div_pos (Nat.le_of_dvd hN hpN) hp.pos
  let : NeZero (N / p) := ⟨hM.ne'⟩
  have hdiv : N ∣ p * (N / p) := by
    rw [Nat.mul_div_cancel' hpN]
  let G : CuspForm (CongruenceSubgroup.Gamma0 (N / p)) 2 :=
    descend hp.ne_zero hdiv g hsupp'
  let F : CuspForm (CongruenceSubgroup.Gamma0 (N / p)) 2 := (p : ℂ) • G
  refine ⟨hpN, hM, F, ?_⟩
  intro n
  have hback : (⇑G ∣[(2 : ℤ)] B p) = ⇑g := by
    dsimp only [G]
    rw [coe_descend, ← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]
  have hfun : (fun τ : ℍ => F (heckeDiagMatrix p • τ)) = ⇑g := by
    funext τ
    have h := congrFun hback τ
    rw [slash_heckeDiagMatrix_apply 2 hp.ne_zero] at h
    change (p : ℂ) * G (heckeDiagMatrix p • τ) = g τ
    simpa only [show (2 : ℤ) - 1 = 1 from rfl, zpow_one] using h
  have hperiod : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 (N / p) : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  have hc := ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul F hperiod hp.ne_zero (p * n)
  rw [hfun, ite_eq_left (dvd_mul_right p n), Nat.mul_div_cancel_left n hp.pos] at hc
  exact hc.symm

end

-- From Solutions/HeckePrimeCoefficients.lean
noncomputable section
open scoped BigOperators ModularForm MatrixGroups Manifold
open UpperHalfPlane

namespace HorizontalPadicL

lemma gammaOne_le_gammaZero (N : ℕ) :
    MTT.GammaOne N ≤ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) :=
  Subgroup.map_mono (CongruenceSubgroup.Gamma1_in_Gamma0 N)

private lemma principal_gammaZero (N : ℕ) (γ : CongruenceSubgroup.Gamma0 N) :
    (1 : DirichletCharacter ℂ N) (γ.val 1 1 : ZMod N) = 1 := by
  apply MulChar.one_apply
  exact (Group.isUnit γ).map (CongruenceSubgroup.Gamma0Map N)

def restrictToGammaOne {N k : ℕ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) (k : ℤ)) :
    CuspForm (MTT.GammaOne N) (k : ℤ) where
  toFun := f
  slash_action_eq' := fun γ hγ ↦ f.slash_action_eq' γ (gammaOne_le_gammaZero N hγ)
  holo' := f.holo'
  zero_at_cusps' := fun hc ↦ f.zero_at_cusps' (hc.mono (gammaOne_le_gammaZero N))

lemma restrictToGammaOne_character_law {N k : ℕ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) (k : ℤ))
    (γ : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    restrictToGammaOne f ((Matrix.SpecialLinearGroup.mapGL ℝ γ.val) • z) =
      (1 : DirichletCharacter ℂ N) (γ.val 1 1 : ZMod N) *
        (((γ.val 1 0 : ℤ) : ℂ) * z + ((γ.val 1 1 : ℤ) : ℂ)) ^ k * restrictToGammaOne f z := by
  rw [principal_gammaZero]
  change f ((Matrix.SpecialLinearGroup.mapGL ℝ γ.val) • z) =
    1 * (((γ.val 1 0 : ℤ) : ℂ) * z + ((γ.val 1 1 : ℤ) : ℂ)) ^ k * f z
  simpa [UpperHalfPlane.denom, Matrix.SpecialLinearGroup.mapGL] using
    SlashInvariantForm.slash_action_eqn'' f
      (show Matrix.SpecialLinearGroup.mapGL ℝ γ.val ∈
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) from
        ⟨γ.val, γ.property, rfl⟩) z

def extendToGammaZero {N k : ℕ} [NeZero N]
    (g : CuspForm (MTT.GammaOne N) (k : ℤ))
    (hg : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane,
      g ((Matrix.SpecialLinearGroup.mapGL ℝ γ.val) • z) =
        (1 : DirichletCharacter ℂ N) (γ.val 1 1 : ZMod N) *
          (((γ.val 1 0 : ℤ) : ℂ) * z + ((γ.val 1 1 : ℤ) : ℂ)) ^ k * g z) :
    CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) (k : ℤ) where
  toFun := g
  slash_action_eq' := by
    intro γ hγ
    obtain ⟨δ, hδ, rfl⟩ := hγ
    ext z
    change ((g : UpperHalfPlane → ℂ) ∣[(k : ℤ)] δ) z = g z
    rw [ModularForm.SL_slash_apply]
    have hgz := hg ⟨δ, hδ⟩ z
    rw [principal_gammaZero] at hgz
    have hgz' : g (δ • z) =
        1 * (((δ 1 0 : ℤ) : ℂ) * z + ((δ 1 1 : ℤ) : ℂ)) ^ k * g z := by
      simpa [Matrix.SpecialLinearGroup.mapGL] using hgz
    rw [hgz']
    simp only [one_mul]
    have hd : (((δ 1 0 : ℤ) : ℂ) * z + ((δ 1 1 : ℤ) : ℂ)) ≠ 0 := by
      simpa [UpperHalfPlane.denom] using UpperHalfPlane.denom_ne_zero δ z
    have hdenom : denom δ z =
        (((δ 1 0 : ℤ) : ℂ) * z + ((δ 1 1 : ℤ) : ℂ)) := by
      simp [UpperHalfPlane.denom]
    rw [hdenom, zpow_neg, zpow_natCast, mul_right_comm,
      mul_inv_cancel₀ (pow_ne_zero _ hd), one_mul]
  holo' := g.holo'
  zero_at_cusps' := by
    intro c hc
    apply g.zero_at_cusps'
    have h1 := (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))).mp hc
    exact (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z (MTT.GammaOne N)).mpr h1

/-- The prime Hecke transform of a weight-two form, including the `U_p` case. -/
theorem exists_cuspFormAtLevel_hecke_qExpansion
    (N : ℕ) (hN : 0 < N) (f : CuspFormAtLevel N hN) (p : ℕ) (hp : p.Prime) :
    ∃ H : CuspFormAtLevel N hN, ∀ n,
      (qExpansion 1 H).coeff n = (qExpansion 1 f).coeff (p * n) +
        (if p ∣ N then 0 else (p : ℂ)) *
          (if p ∣ n then (qExpansion 1 f).coeff (n / p) else 0) := by
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  obtain ⟨g, hg, hgχ⟩ := MTT.exists_cuspForm_heckePrime_pos hN (by decide : 1 ≤ 2)
    (1 : DirichletCharacter ℂ N) (restrictToGammaOne f)
    (restrictToGammaOne_character_law f) p hp
  let H := extendToGammaZero g hgχ
  have hper : (1 : ℝ) ∈
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp
  have hprincipal : (1 : DirichletCharacter ℂ N) (p : ZMod N) * (p : ℂ) ^ (2 - 1) =
      (if p ∣ N then 0 else (p : ℂ)) := by
    by_cases h : p ∣ N
    · have hu : ¬ IsUnit (p : ZMod N) := by
        rw [ZMod.isUnit_iff_coprime, hp.coprime_iff_not_dvd]
        exact not_not.mpr h
      simp [h, MulChar.map_nonunit _ hu]
    · have hu : IsUnit (p : ZMod N) :=
        (ZMod.isUnit_iff_coprime p N).mpr (hp.coprime_iff_not_dvd.mpr h)
      simp [h, MulChar.one_apply hu]
  refine ⟨H, fun n ↦ ?_⟩
  have hs : ∀ τ : UpperHalfPlane,
      HasSum (fun n ↦ ((qExpansion 1 f).coeff (p * n) +
        (1 : DirichletCharacter ℂ N) (p : ZMod N) * (p : ℂ) ^ (2 - 1) *
          (if p ∣ n then (qExpansion 1 f).coeff (n / p) else 0)) •
            Function.Periodic.qParam 1 (τ : ℂ) ^ n) (H τ) := by
    intro τ
    change HasSum _ (g τ)
    rw [hg]
    change HasSum _ (MTT.heckePrime 2 _ p f τ)
    exact MTT.hasSum_heckePrime 2 _ hp f (fun n ↦ (qExpansion 1 f).coeff n) τ
      (fun σ ↦ by
        simpa only [smul_eq_mul] using ModularForm.hasSum_qExpansion f zero_lt_one hper σ)
  have hc := ModularFormClass.qExpansion_coeff_unique zero_lt_one hper hs n
  rw [hprincipal] at hc
  exact hc.symm

end HorizontalPadicL

end

-- From Solutions/MinimalLevelReduction.lean
noncomputable section

open UpperHalfPlane

namespace HorizontalPadicL

lemma qExpansion_coeff_smul {N : ℕ} (hN : 0 < N)
    (f : CuspFormAtLevel N hN) (c : ℂ) (n : ℕ) :
    (qExpansion 1 (c • f : CuspFormAtLevel N hN)).coeff n =
      c * (qExpansion 1 f).coeff n := by
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  change (qExpansion 1 (c • (⇑f : UpperHalfPlane → ℂ))).coeff n = _
  rw [ModularForm.qExpansion_smul one_pos (by simp) c f]
  simp

lemma qExpansion_coeff_sub {N : ℕ} (hN : 0 < N)
    (f g : CuspFormAtLevel N hN) (n : ℕ) :
    (qExpansion 1 (f - g : CuspFormAtLevel N hN)).coeff n =
      (qExpansion 1 f).coeff n - (qExpansion 1 g).coeff n := by
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  change (qExpansion 1 (⇑f - ⇑g)).coeff n = _
  rw [ModularForm.qExpansion_sub one_pos (by simp) f g]
  simp

lemma modularConductor_recurrence_parameter
    (E : WeierstrassCurve ℚ) (hmod : IsModular E) (p : ℕ) (hp : p.Prime)
    (b : ℤ) (hrec : ∀ n : ℕ, E.LFunction (p * n) =
      E.LFunction p * E.LFunction n - if p ∣ n then b * E.LFunction (n / p) else 0)
    (hHecke : ∀ (N : ℕ) (hN : 0 < N) (f : CuspFormAtLevel N hN),
      ∃ H : CuspFormAtLevel N hN, ∀ n : ℕ,
        (qExpansion 1 H).coeff n = (qExpansion 1 f).coeff (p * n) +
          (if p ∣ N then 0 else (p : ℂ)) *
            (if p ∣ n then (qExpansion 1 f).coeff (n / p) else 0))
    (hDescent : ∀ (N : ℕ) (hN : 0 < N) (g : CuspFormAtLevel N hN),
      (qExpansion 1 g).coeff p ≠ 0 →
      (∀ n : ℕ, ¬ p ∣ n → (qExpansion 1 g).coeff n = 0) →
      p ∣ N ∧ ∃ hM : 0 < N / p, ∃ f : CuspFormAtLevel (N / p) hM,
        ∀ n : ℕ, (qExpansion 1 f).coeff n = (qExpansion 1 g).coeff (p * n)) :
    (b : ℂ) = if p ∣ modularConductor E hmod then 0 else (p : ℂ) := by
  classical
  let N := modularConductor E hmod
  let F := modularFormAtConductor E hmod
  let f := F.form
  have hf (n : ℕ) : (qExpansion 1 f).coeff n = (E.LFunction n : ℂ) :=
    (F.coeff_eq n).symm
  obtain ⟨H, hH⟩ := hHecke N F.level_pos f
  let c : ℂ := (if p ∣ N then 0 else (p : ℂ)) - b
  by_contra h
  have hc : c ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  let g : CuspFormAtLevel N F.level_pos := c⁻¹ • (H - (E.LFunction p : ℂ) • f)
  have hg (n : ℕ) : (qExpansion 1 g).coeff n =
      if p ∣ n then (E.LFunction (n / p) : ℂ) else 0 := by
    dsimp only [g]
    rw [qExpansion_coeff_smul, qExpansion_coeff_sub, qExpansion_coeff_smul, hH]
    simp only [hf]
    have hr : (E.LFunction (p * n) : ℂ) =
        (E.LFunction p : ℂ) * (E.LFunction n : ℂ) -
          if p ∣ n then (b : ℂ) * (E.LFunction (n / p) : ℂ) else 0 := by
      exact_mod_cast hrec n
    rw [hr]
    by_cases hn : p ∣ n
    · simp only [ite_eq_left hn]
      change c⁻¹ * (_ + _ - _) = _
      have heq : (E.LFunction p : ℂ) * (E.LFunction n : ℂ) -
          (b : ℂ) * (E.LFunction (n / p) : ℂ) +
          (if p ∣ N then 0 else (p : ℂ)) * (E.LFunction (n / p) : ℂ) -
          (E.LFunction p : ℂ) * (E.LFunction n : ℂ) =
            c * (E.LFunction (n / p) : ℂ) := by dsimp [c]; ring
      rw [heq, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    · simp [hn]
  have hgp : (qExpansion 1 g).coeff p ≠ 0 := by
    rw [hg]
    simp [Nat.div_self hp.pos]
  obtain ⟨_, hM, fM, hfM⟩ := hDescent N F.level_pos g hgp (by
    intro n hn
    simp [hg, hn])
  have hmodM : Nonempty (ModularFormAtLevel E (N / p)) := by
    refine ⟨⟨hM, fM, fun n ↦ ?_⟩⟩
    rw [hfM, hg, ite_eq_left (dvd_mul_right p n), Nat.mul_div_cancel_left n hp.pos]
  have hmin : N ≤ N / p := Nat.find_min' hmod hmodM
  exact (not_le_of_gt (Nat.div_lt_self F.level_pos hp.one_lt)) hmin

end HorizontalPadicL

end

-- From Solutions/MinimalLevelSolution.lean
noncomputable section

open HorizontalPadicL

theorem solution (E : WeierstrassCurve ℚ) [E.IsElliptic] (hmod : IsModular E)
    (p : ℕ) (hp : p.Prime) :
    (p ∣ modularConductor E hmod ↔ LocalEulerFactorDegreeBelowTwo E p) := by
  have hparameter (b : ℤ) (hrec : ∀ n : ℕ, E.LFunction (p * n) =
      E.LFunction p * E.LFunction n - if p ∣ n then b * E.LFunction (n / p) else 0) :
      (b : ℂ) = if p ∣ modularConductor E hmod then 0 else (p : ℂ) :=
    modularConductor_recurrence_parameter E hmod p hp b hrec
      (fun N hN f ↦ exists_cuspFormAtLevel_hecke_qExpansion N hN f p hp)
      (fun _ hN g hg hsupp ↦
        CuspForm.exists_qExpansion_descent_of_prime_support hN hp g hg hsupp)
  constructor
  · intro hdiv
    rcases localEulerFactorDegree_dichotomy E hp with hlin | hquad
    · exact hlin
    · have hb := hparameter p (fun n ↦ hquad.LFunction_prime_mul hp n)
      simp only [Int.cast_natCast, ite_eq_left hdiv] at hb
      exact False.elim (hp.ne_zero (by exact_mod_cast hb))
  · intro hlin
    have hb := hparameter 0 (by simpa using hlin.LFunction_prime_mul hp)
    by_contra hnot
    simp only [Int.cast_zero, ite_eq_right hnot] at hb
    exact hp.ne_zero (by exact_mod_cast hb.symm)

end
