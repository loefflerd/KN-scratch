import Definitions.FLT.Def_Gamma0CoeffCohomology
import Definitions.FLT.Def_HeckeEis_BinaryFormRep
import Definitions.MTT.Def_MTT_ParabolicCohomology
import Definitions.FLT.Def_ModularCurve_PeriodMap
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Tactic
import Mathlib.Tactic.LinearCombination
import Theorems.FLT.Thm_HeckeEis_exists_eichlerShimura_coeffH1par_binaryFormRepSL
import Theorems.FLT.Thm_ModularForm_finiteDimensional_of_isArithmetic

/-! # The index change on adjoining the central involution -/

open scoped MatrixGroups

namespace MTT.Cohomology

theorem mem_sup_neg_one_iff (H : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) :
    g ∈ H ⊔ Subgroup.zpowers (-1) ↔ g ∈ H ∨ -g ∈ H := by
  let K : Subgroup SL(2, ℤ) :=
    { carrier := {g | g ∈ H ∨ -g ∈ H}
      one_mem' := Or.inl H.one_mem
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (H.mul_mem ha hb)
        · exact Or.inr (by simpa using H.mul_mem ha hb)
        · exact Or.inr (by simpa using H.mul_mem ha hb)
        · exact Or.inl (by simpa using H.mul_mem ha hb)
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (H.inv_mem ha)
        · exact Or.inr (by simpa using H.inv_mem ha) }
  have hle : H ⊔ Subgroup.zpowers (-1) ≤ K := by
    refine sup_le (fun _ h => Or.inl h) (Subgroup.zpowers_le.mpr ?_)
    exact Or.inr (by simpa only [neg_neg] using H.one_mem)
  refine ⟨fun h => hle h, ?_⟩
  rintro (h | h)
  · exact Subgroup.mem_sup_left h
  · have hm := Subgroup.mul_mem_sup h (Subgroup.mem_zpowers (-1 : SL(2, ℤ)))
    simpa using hm

end MTT.Cohomology

/-! # Retraction after adjoining a disjoint central sign -/

noncomputable section

open scoped MatrixGroups Classical

namespace MTT.Cohomology

variable (H : Subgroup SL(2, ℤ)) (hz : (-1 : SL(2, ℤ)) ∉ H)

include hz in
theorem eq_of_eq_or_neg {a b : SL(2, ℤ)} (ha : a ∈ H) (hb : b ∈ H)
    (hab : a = b ∨ a = -b) : a = b := by
  rcases hab with h | h
  · exact h
  · exfalso
    apply hz
    have hm := H.mul_mem ha (H.inv_mem hb)
    simpa only [h, neg_mul, mul_inv_cancel] using hm

def centralSignRep (g : (H ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ))) : H :=
  if hg : g.val ∈ H then ⟨g.val, hg⟩ else
    ⟨-g.val, ((mem_sup_neg_one_iff H g.val).mp g.property).resolve_left hg⟩

theorem centralSignRep_eq_or (g : (H ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ))) :
    (centralSignRep H g).val = g.val ∨ (centralSignRep H g).val = -g.val := by
  by_cases hg : g.val ∈ H <;> simp [centralSignRep, hg]

def centralSignRetraction : (H ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) →* H where
  toFun := centralSignRep H
  map_one' := by
    apply Subtype.ext
    simp [centralSignRep, H.one_mem]
  map_mul' g h := by
    apply Subtype.ext
    apply eq_of_eq_or_neg H hz (centralSignRep H (g * h)).property
      (H.mul_mem (centralSignRep H g).property (centralSignRep H h).property)
    rcases centralSignRep_eq_or H (g * h) with hgh | hgh <;>
      rcases centralSignRep_eq_or H g with hg | hg <;>
      rcases centralSignRep_eq_or H h with hh | hh <;>
      simp only [Subgroup.coe_mul] at hgh ⊢ <;> simp [hgh, hg, hh]

theorem centralSignRetraction_inclusion (g : H) :
    centralSignRetraction H hz (Subgroup.inclusion le_sup_left g) = g := by
  apply Subtype.ext
  simp [centralSignRetraction, centralSignRep, g.property]

end MTT.Cohomology

/-! # Adjoining the central sign at levels three and four -/

open scoped MatrixGroups

namespace MTT.Cohomology

theorem gammaOne_neg_one_not_mem_of_three_le {N : ℕ} (hN : 3 ≤ N) :
    (-1 : SL(2, ℤ)) ∉ CongruenceSubgroup.Gamma1 N := by
  intro h
  have ha := ((CongruenceSubgroup.Gamma1_mem N _).mp h).1
  have hc : ((-1 : ℤ) : ZMod N) = (1 : ℤ) := by simpa using ha
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub (-1) 1 N).mp hc
  have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt (by norm_num : (0 : ℤ) ≤ 1 - -1)
    (by omega : (1 : ℤ) - -1 < N) hd
  norm_num at hz

theorem gammaOne_sup_neg_one_eq_gammaZero {N : ℕ} (hN : 3 ≤ N) (hN' : N ≤ 4) :
    CongruenceSubgroup.Gamma1 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) =
      CongruenceSubgroup.Gamma0 N := by
  apply le_antisymm
  · refine sup_le (CongruenceSubgroup.Gamma1_in_Gamma0 N) (Subgroup.zpowers_le.mpr ?_)
    rw [CongruenceSubgroup.Gamma0_mem]
    simp
  · intro g hg
    rw [mem_sup_neg_one_iff]
    have hc := CongruenceSubgroup.Gamma0_mem.mp hg
    have hdet : (g 0 0 : ZMod N) * g 1 1 = 1 := by
      have hd := g.property
      rw [Matrix.det_fin_two] at hd
      have he := congrArg (Int.castRingHom (ZMod N)) hd
      simpa only [map_sub, map_mul, map_one, Int.coe_castRingHom, hc, mul_zero,
        sub_zero] using he
    have hunits : ∀ a b : ZMod N, a * b = 1 →
        (a = 1 ∧ b = 1) ∨ (a = -1 ∧ b = -1) := by
      have h : N = 3 ∨ N = 4 := by omega
      rcases h with rfl | rfl <;> decide
    rcases hunits _ _ hdet with hab | hab
    · exact Or.inl ((CongruenceSubgroup.Gamma1_mem N g).mpr ⟨hab.1, hab.2, hc⟩)
    · apply Or.inr
      rw [CongruenceSubgroup.Gamma1_mem]
      simpa only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg,
        hab.1, hab.2, hc, neg_neg, neg_zero] using
        (show (1 : ZMod N) = 1 ∧ (1 : ZMod N) = 1 ∧ (0 : ZMod N) = 0 from
          ⟨rfl, rfl, rfl⟩)

end MTT.Cohomology

/-! # From degree-zero MTT cocycles to scalar parabolic homomorphisms

The comparison uses only the definitions: degree-zero homogeneous polynomials
are constants, and an integral determinant-one matrix of trace squared four
fixes a rational cusp. No period-map injectivity is used.
-/

section

namespace MTT.Cohomology

open Matrix

theorem exists_cusp_fixed_of_trace_sq (g : SpecialLinearGroup (Fin 2) ℤ)
    (hg : g.val.trace ^ 2 = 4) : ∃ x : Cusp, cuspAct g x = x := by
  let a := SpecialLinearGroup.mapGL ℚ g
  by_cases hc : a 1 0 = 0
  · exact ⟨OnePoint.infty, OnePoint.smul_infty_eq_self_iff.mpr hc⟩
  · refine ⟨((a 0 0 - a 1 1) / (2 * a 1 0) : ℚ), ?_⟩
    change a • (((a 0 0 - a 1 1) / (2 * a 1 0) : ℚ) : Cusp) = _
    apply GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff.mp
    have hdet : a 0 0 * a 1 1 - a 0 1 * a 1 0 = 1 := by
      have h := g.property
      rw [det_fin_two] at h
      change (g 0 0 : ℚ) * g 1 1 - g 0 1 * g 1 0 = 1
      exact_mod_cast h
    have htrace : (a 0 0 + a 1 1) ^ 2 = 4 := by
      rw [trace_fin_two] at hg
      change ((g 0 0 : ℚ) + g 1 1) ^ 2 = 4
      exact_mod_cast hg
    simp only [GeneralLinearGroup.fixpointPolynomial, map_sub, map_add, map_mul,
      Polynomial.aeval_X_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_self_apply]
    field_simp
    linear_combination -htrace + 4 * hdet

end MTT.Cohomology

/-! # Comparing the MTT and existing binary-form coefficient cohomology models -/

section

open scoped MatrixGroups

namespace MTT.Cohomology

theorem act_eq_binarySubst (g : Matrix (Fin 2) (Fin 2) ℤ) (P : Binary ℂ) :
    act g P = HeckeEis.binarySubst ℂ g P := by
  simp only [act, HeckeEis.binarySubst, MvPolynomial.C_mul', AlgHom.toLinearMap_apply]

abbrev binaryCoeffRep (N n : ℕ) :=
  (HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma1 N).subtype

theorem gammaOneRep_apply_eq_binaryCoeffRep (N n : ℕ)
    (g : CongruenceSubgroup.Gamma1 N) (P : gammaOneRep N n) :
    (gammaOneRep N n).ρ g P = binaryCoeffRep N n g P :=
  Subtype.ext (act_eq_binarySubst g.val.val P.val)

end MTT.Cohomology

/-! # The global symmetric-power representation underlying the MTT coefficients -/

section

open scoped MatrixGroups

namespace MTT.Cohomology

def fullSymRep (n : ℕ) : Rep ℂ SL(2, ℤ) :=
  Rep.of ((symRepresentation ⊤ n ℂ).ρ.comp
    { toFun := fun g => ⟨g, Subgroup.mem_top g⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl })

theorem gammaOneRep_eq_res_fullSymRep (N n : ℕ) :
    gammaOneRep N n = Rep.res (CongruenceSubgroup.Gamma1 N).subtype (fullSymRep n) := rfl

end MTT.Cohomology

namespace MTT.Cohomology

open MvPolynomial

theorem bind_smul_X_of_homogeneous {R : Type*} [CommRing R] {n : ℕ}
    {P : Binary R} (hP : P.IsHomogeneous n) (a : R) :
    bind₁ (fun i => a • X i) P = a ^ n • P := by
  classical
  induction hP using IsWeightedHomogeneous.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add P Q hP hQ ihP ihQ => rw [map_add, ihP, ihQ, smul_add]
  | monomial d r hd =>
      rw [bind₁_monomial]
      simp only [Algebra.smul_def, algebraMap_eq, mul_pow, Finset.prod_mul_distrib,
        ← map_pow, ← map_prod]
      rw [Finset.prod_pow_eq_pow_sum]
      have hdeg : ∑ i ∈ d.support, d i = n := by
        simpa only [Finsupp.weight_apply, Finsupp.sum,
          Pi.one_apply, smul_eq_mul, mul_one] using hd
      rw [hdeg, monomial_eq, Finsupp.prod]
      ring

theorem act_neg_one_of_homogeneous {R : Type*} [CommRing R] {n : ℕ}
    {P : Binary R} (hP : P ∈ Sym R n) : act (-1) P = (-1 : R) ^ n • P := by
  change bind₁ (fun i : Fin 2 => ∑ a : Fin 2,
    ((-1 : Matrix (Fin 2) (Fin 2) ℤ) a i : R) • X a) P = _
  have hvars : (fun i : Fin 2 => ∑ a : Fin 2,
      ((-1 : Matrix (Fin 2) (Fin 2) ℤ) a i : R) • X a) =
      (fun i : Fin 2 => (-1 : R) • (X i : Binary R)) := by
    funext i
    fin_cases i <;> simp [Matrix.one_apply]
  rw [hvars]
  exact bind_smul_X_of_homogeneous hP (-1)

end MTT.Cohomology

/-! # Even-degree coefficient comparison at levels three and four -/

section

open scoped MatrixGroups

namespace MTT.Cohomology

def smallLevelRetraction {N : ℕ} (hN : 3 ≤ N) (hN' : N ≤ 4) :
    CongruenceSubgroup.Gamma0 N →* CongruenceSubgroup.Gamma1 N :=
  (centralSignRetraction (CongruenceSubgroup.Gamma1 N)
    (gammaOne_neg_one_not_mem_of_three_le hN)).comp
      (MulEquiv.subgroupCongr (gammaOne_sup_neg_one_eq_gammaZero hN hN').symm).toMonoidHom

theorem smallLevelRetraction_eq_or {N : ℕ} (hN : 3 ≤ N) (hN' : N ≤ 4)
    (g : CongruenceSubgroup.Gamma0 N) :
    (smallLevelRetraction hN hN' g).val = g.val ∨
      (smallLevelRetraction hN hN' g).val = -g.val :=
  centralSignRep_eq_or (CongruenceSubgroup.Gamma1 N) _

theorem smallLevelRetraction_inclusion {N : ℕ} (hN : 3 ≤ N) (hN' : N ≤ 4)
    (g : CongruenceSubgroup.Gamma1 N) :
    smallLevelRetraction hN hN' (Subgroup.inclusion (CongruenceSubgroup.Gamma1_in_Gamma0 N) g) =
      g := by
  apply Subtype.ext
  simp [smallLevelRetraction, centralSignRetraction, centralSignRep, g.property]

theorem fullSymRep_neg_of_even {n : ℕ} (hn : Even n) (g : SL(2, ℤ)) :
    (fullSymRep n).ρ (-g) = (fullSymRep n).ρ g := by
  have hz : (fullSymRep n).ρ (-1) = 1 := by
    apply LinearMap.ext
    intro P
    apply Subtype.ext
    change act (-1) P.val = P.val
    rw [act_neg_one_of_homogeneous P.property, hn.neg_one_pow, one_smul]
  rw [← neg_one_mul g, map_mul, hz, one_mul]

theorem smallLevelRetraction_action {N n : ℕ} (hN : 3 ≤ N) (hN' : N ≤ 4)
    (hn : Even n) (g : CongruenceSubgroup.Gamma0 N) (P : gammaOneRep N n) :
    (gammaOneRep N n).ρ (smallLevelRetraction hN hN' g) P =
      HeckeEis.binaryFormRepSL ℂ n g.val P := by
  change (fullSymRep n).ρ (smallLevelRetraction hN hN' g).val P = _
  rcases smallLevelRetraction_eq_or hN hN' g with hg | hg
  · rw [hg]
    exact Subtype.ext (act_eq_binarySubst g.val.val P.val)
  · rw [hg, fullSymRep_neg_of_even hn]
    exact Subtype.ext (act_eq_binarySubst g.val.val P.val)

theorem smallLevelRetraction_trace_sq {N : ℕ} (hN : 3 ≤ N) (hN' : N ≤ 4)
    (g : CongruenceSubgroup.Gamma0 N) :
    Matrix.trace (smallLevelRetraction hN hN' g).val.val ^ 2 = Matrix.trace g.val.val ^ 2 := by
  rcases smallLevelRetraction_eq_or hN hN' g with hg | hg
  · rw [hg]
  · rw [hg, Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg, neg_sq]

def evenToGammaZeroParabolic {N n : ℕ} (hN : 3 ≤ N) (hN' : N ≤ 4) (hn : Even n) :
    parabolicCocycles N n →ₗ[ℂ] HeckeEis.coeffParabolicCocycles
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) where
  toFun c := ⟨fun g => c.val (smallLevelRetraction hN hN' g), by
    have hc := (mem_parabolicCocycles_iff c.val).mp c.property
    constructor
    · intro g h
      have hmul := congrArg c.val ((smallLevelRetraction hN hN').map_mul g h)
      have hcoc := hc.1 (smallLevelRetraction hN hN' g) (smallLevelRetraction hN hN' h)
      have hact := smallLevelRetraction_action hN hN' hn g
        (c.val (smallLevelRetraction hN hN' h))
      exact hmul.trans (hcoc.trans ((congrArg
        (fun Q : gammaOneRep N n => Q + c.val (smallLevelRetraction hN hN' g)) hact).trans
          (add_comm _ _)))
    · intro g hg
      have hr : Matrix.trace (smallLevelRetraction hN hN' g).val.val ^ 2 = 4 := by
        rwa [smallLevelRetraction_trace_sq]
      obtain ⟨x, hx⟩ := exists_cusp_fixed_of_trace_sq (smallLevelRetraction hN hN' g).val hr
      obtain ⟨P, hP⟩ := hc.2 x _ hx
      refine ⟨P, ?_⟩
      rw [smallLevelRetraction_action hN hN' hn] at hP
      exact hP.symm⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def evenToGammaZeroClass {N n : ℕ} (hN : 3 ≤ N) (hN' : N ≤ 4) (hn : Even n) :
    parabolicCocycles N n →ₗ[ℂ] HeckeEis.coeffH1par
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) :=
  (HeckeEis.coeffH1parMk _).comp (evenToGammaZeroParabolic hN hN' hn)

theorem evenToGammaZeroClass_ker {N n : ℕ} (hN : 3 ≤ N) (hN' : N ≤ 4) (hn : Even n) :
    (evenToGammaZeroClass hN hN' hn).ker = parabolicCoboundaries N n := by
  ext c
  change HeckeEis.coeffH1parMk _ (evenToGammaZeroParabolic hN hN' hn c) = 0 ↔ _
  rw [HeckeEis.coeffH1parMk_eq_zero_iff, HeckeEis.mem_coeffCoboundaries_iff,
    mem_parabolicCoboundaries_iff]
  constructor
  · rintro ⟨P, hP⟩
    refine ⟨P, fun g => ?_⟩
    have hg := congrFun hP (Subgroup.inclusion (CongruenceSubgroup.Gamma1_in_Gamma0 N) g)
    change HeckeEis.binaryFormRepSL ℂ n g.val P - P =
      c.val (smallLevelRetraction hN hN'
        (Subgroup.inclusion (CongruenceSubgroup.Gamma1_in_Gamma0 N) g)) at hg
    rw [smallLevelRetraction_inclusion] at hg
    have he := gammaOneRep_apply_eq_binaryCoeffRep N n g P
    exact hg.symm.trans (congrArg
      (fun Q : gammaOneRep N n => Q - (show gammaOneRep N n from P)) he.symm)
  · rintro ⟨P, hP⟩
    refine ⟨P, funext fun g => ?_⟩
    have hp := hP (smallLevelRetraction hN hN' g)
    rw [smallLevelRetraction_action hN hN' hn] at hp
    exact hp.symm

def evenToGammaZeroH1 {N n : ℕ} (hN : 3 ≤ N) (hN' : N ≤ 4) (hn : Even n) :
    ParabolicH1 N n →ₗ[ℂ] HeckeEis.coeffH1par
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) :=
  (parabolicCoboundaries N n).liftQ (evenToGammaZeroClass hN hN' hn)
    (evenToGammaZeroClass_ker hN hN' hn).ge

theorem evenToGammaZeroH1_injective {N n : ℕ} (hN : 3 ≤ N) (hN' : N ≤ 4) (hn : Even n) :
    Function.Injective (evenToGammaZeroH1 hN hN' hn) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot _ _ _ (evenToGammaZeroClass_ker hN hN' hn).le

end MTT.Cohomology

/-! # Restriction of cusp forms to a smaller subgroup -/

namespace CuspForm

variable {Γ Δ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

variable [Γ.HasDetOne] [Δ.HasDetOne]

def restrictSubgroup (hΓ : Γ ≤ Δ) : CuspForm Δ k →ₗ[ℂ] CuspForm Γ k where
  toFun f :=
    { toFun := f
      slash_action_eq' := fun g hg => f.slash_action_eq' g (hΓ hg)
      holo' := f.holo'
      zero_at_cusps' := fun hc => f.zero_at_cusps' (IsCusp.mono hΓ hc) }
  map_add' _ _ := CuspForm.ext fun _ => rfl
  map_smul' _ _ := CuspForm.ext fun _ => rfl

theorem restrictSubgroup_injective (hΓ : Γ ≤ Δ) :
    Function.Injective (restrictSubgroup (k := k) hΓ) := by
  intro f g h
  exact CuspForm.ext fun z => congrArg (fun F : CuspForm Γ k => F z) h

theorem finrank_le_of_subgroup_le (hΓ : Γ ≤ Δ) [FiniteDimensional ℂ (CuspForm Γ k)] :
    Module.finrank ℂ (CuspForm Δ k) ≤ Module.finrank ℂ (CuspForm Γ k) :=
  LinearMap.finrank_le_finrank_of_injective (restrictSubgroup_injective hΓ)

end CuspForm

/-! # The level-two dimension bound via the existing Gamma0 decomposition -/

section

open scoped MatrixGroups

namespace MTT.Cohomology

theorem gammaZero_binaryCoeffH1_dimension (N n : ℕ) [NeZero N] :
    FiniteDimensional ℂ (HeckeEis.coeffH1par
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)) ∧
    Module.finrank ℂ (HeckeEis.coeffH1par
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)) =
      2 * Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) := by
  have := ModularForm.finiteDimensional_of_isArithmetic
    ((CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) ((n : ℤ) + 2)
  have : FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) :=
    FiniteDimensional.of_injective CuspForm.toModularFormₗ CuspForm.toModularFormₗ_injective
  obtain ⟨f, g, hf, hg, hc, _⟩ :=
    HeckeEis.exists_eichlerShimura_coeffH1par_binaryFormRepSL N n
  have : Module.Finite ℂ g.range :=
    Module.Finite.of_surjective g.rangeRestrict g.surjective_rangeRestrict
  have hfin := Module.Finite.equiv (Submodule.prodEquivOfIsCompl _ _ hc)
  refine ⟨hfin, ?_⟩
  have hd := Submodule.finrank_add_eq_of_isCompl hc
  have hgr : Module.finrank ℂ g.range =
      Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) := by
    have hr := rank_eq_of_equiv_equiv (starRingEnd ℂ)
      (LinearEquiv.ofInjective g hg).toAddEquiv (starRingAut : ℂ ≃+* ℂ).bijective
      (fun r x => (LinearEquiv.ofInjective g hg).map_smul' r x)
    exact (congrArg Cardinal.toNat hr).symm
  rw [LinearMap.finrank_range_of_inj hf, hgr] at hd
  omega

end MTT.Cohomology

/-! # The even-weight dimension bound at levels three and four -/

namespace MTT.Cohomology

theorem solution {N k : ℕ}
    (hN : 3 ≤ N) (hN' : N ≤ 4) (hk : 3 ≤ k) (hke : Even k) :
    Module.finrank ℂ (ParabolicH1 N (k - 2)) ≤
      2 * Module.finrank ℂ (CuspForm (MTT.GammaOne N) (k : ℤ)) := by
  have : NeZero N := ⟨by omega⟩
  have hn : Even (k - 2) := by
    obtain ⟨m, hm⟩ := hke
    exact ⟨m - 1, by omega⟩
  have hd := gammaZero_binaryCoeffH1_dimension N (k - 2)
  have := hd.1
  have hcoh := LinearMap.finrank_le_finrank_of_injective
    (evenToGammaZeroH1_injective hN hN' hn)
  have hw : ((k - 2 : ℕ) : ℤ) + 2 = k := by omega
  rw [hd.2, hw] at hcoh
  have := ModularForm.finiteDimensional_of_isArithmetic (MTT.GammaOne N) (k : ℤ)
  have : FiniteDimensional ℂ (CuspForm (MTT.GammaOne N) (k : ℤ)) :=
    FiniteDimensional.of_injective CuspForm.toModularFormₗ CuspForm.toModularFormₗ_injective
  have hlevel : MTT.GammaOne N ≤
      (CongruenceSubgroup.Gamma0 N).map (Matrix.SpecialLinearGroup.mapGL ℝ) :=
    Subgroup.map_mono (CongruenceSubgroup.Gamma1_in_Gamma0 N)
  have hf := CuspForm.finrank_le_of_subgroup_le (k := (k : ℤ)) hlevel
  exact hcoh.trans (Nat.mul_le_mul_left 2 hf)

end MTT.Cohomology

export MTT.Cohomology (solution)
