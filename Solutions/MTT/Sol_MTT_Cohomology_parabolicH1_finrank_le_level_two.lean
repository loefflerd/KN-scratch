import Definitions.MTT.Def_MTT_ParabolicCohomology
import Definitions.FLT.Def_Gamma0CoeffCohomology
import Definitions.FLT.Def_HeckeEis_BinaryFormRep
import Theorems.FLT.Thm_HeckeEis_exists_eichlerShimura_coeffH1par_binaryFormRepSL
import Theorems.FLT.Thm_ModularForm_finiteDimensional_of_isArithmetic
import Mathlib.Tactic.LinearCombination

/-! # The MTT parabolic-cohomology dimension bound at level two

We compare coefficient conventions and use the existing Gamma0
Eichler--Shimura decomposition, preserving its conjugate-linear summand.
-/

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups

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

theorem act_eq_binarySubst (g : Matrix (Fin 2) (Fin 2) ℤ) (P : Binary ℂ) :
    act g P = HeckeEis.binarySubst ℂ g P := by
  simp only [act, HeckeEis.binarySubst, MvPolynomial.C_mul', AlgHom.toLinearMap_apply]

abbrev binaryCoeffRep (N n : ℕ) :=
  (HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma1 N).subtype

theorem gammaOneRep_apply_eq_binaryCoeffRep (N n : ℕ)
    (g : CongruenceSubgroup.Gamma1 N) (P : gammaOneRep N n) :
    (gammaOneRep N n).ρ g P = binaryCoeffRep N n g P :=
  Subtype.ext (act_eq_binarySubst g.val.val P.val)

def toBinaryCoeffParabolic (N n : ℕ) : parabolicCocycles N n →ₗ[ℂ]
    HeckeEis.coeffParabolicCocycles (binaryCoeffRep N n) where
  toFun c := ⟨c.val, by
    have hc := (mem_parabolicCocycles_iff c.val).mp c.property
    constructor
    · intro g h
      rw [hc.1, gammaOneRep_apply_eq_binaryCoeffRep]
      exact add_comm _ _
    · intro g hg
      obtain ⟨x, hx⟩ := exists_cusp_fixed_of_trace_sq g.val hg
      obtain ⟨P, hP⟩ := hc.2 x g hx
      refine ⟨P, ?_⟩
      apply Subtype.ext
      change HeckeEis.binarySubst ℂ g.val.val P.val - P.val = (c.val g).val
      rw [← act_eq_binarySubst]
      exact (congrArg (fun Q : gammaOneRep N n => Q.val) hP).symm⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def toBinaryCoeffClass (N n : ℕ) : parabolicCocycles N n →ₗ[ℂ]
    HeckeEis.coeffH1par (binaryCoeffRep N n) :=
  (HeckeEis.coeffH1parMk _).comp (toBinaryCoeffParabolic N n)

theorem toBinaryCoeffClass_ker (N n : ℕ) :
    (toBinaryCoeffClass N n).ker = parabolicCoboundaries N n := by
  ext c
  change HeckeEis.coeffH1parMk _ (toBinaryCoeffParabolic N n c) = 0 ↔ _
  rw [HeckeEis.coeffH1parMk_eq_zero_iff, HeckeEis.mem_coeffCoboundaries_iff,
    mem_parabolicCoboundaries_iff]
  constructor
  · rintro ⟨P, hP⟩
    refine ⟨P, fun g => ?_⟩
    rw [gammaOneRep_apply_eq_binaryCoeffRep N n g P]
    exact (congrFun hP g).symm
  · rintro ⟨P, hP⟩
    refine ⟨P, funext fun g => ?_⟩
    rw [← gammaOneRep_apply_eq_binaryCoeffRep]
    exact (hP g).symm

def toBinaryCoeffH1 (N n : ℕ) : ParabolicH1 N n →ₗ[ℂ]
    HeckeEis.coeffH1par (binaryCoeffRep N n) :=
  (parabolicCoboundaries N n).liftQ (toBinaryCoeffClass N n)
    (toBinaryCoeffClass_ker N n).ge

theorem toBinaryCoeffH1_injective (N n : ℕ) : Function.Injective (toBinaryCoeffH1 N n) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot _ _ _ (toBinaryCoeffClass_ker N n).le

theorem parabolicH1_finrank_le_binaryCoeffH1 (N n : ℕ)
    [FiniteDimensional ℂ (HeckeEis.coeffH1par (binaryCoeffRep N n))] :
    Module.finrank ℂ (ParabolicH1 N n) ≤
      Module.finrank ℂ (HeckeEis.coeffH1par (binaryCoeffRep N n)) :=
  LinearMap.finrank_le_finrank_of_injective (toBinaryCoeffH1_injective N n)

theorem gammaOne_two_eq_gammaZero_two :
    CongruenceSubgroup.Gamma1 2 = CongruenceSubgroup.Gamma0 2 := by
  ext g
  rw [CongruenceSubgroup.Gamma1_mem, CongruenceSubgroup.Gamma0_mem]
  refine ⟨fun h => h.2.2, fun hc => ?_⟩
  have hd : (g 0 0 : ZMod 2) * (g 1 1 : ZMod 2) = 1 := by
    have hdet := g.property
    rw [Matrix.det_fin_two] at hdet
    have hdet' : (g 0 0 : ZMod 2) * g 1 1 - (g 0 1 : ZMod 2) * g 1 0 = 1 := by
      have h := congrArg (Int.castRingHom (ZMod 2)) hdet
      simpa only [map_sub, map_mul, map_one, Int.coe_castRingHom] using h
    simpa only [hc, mul_zero, sub_zero] using hdet'
  refine ⟨?_, ?_, hc⟩
  · have : ∀ a b : ZMod 2, a * b = 1 → a = 1 := by decide
    exact this _ _ hd
  · have : ∀ a b : ZMod 2, a * b = 1 → b = 1 := by decide
    exact this _ _ hd

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

theorem parabolicH1_finrank_le_level_two {k : ℕ} (hk : 2 ≤ k) :
    Module.finrank ℂ (ParabolicH1 2 (k - 2)) ≤
      2 * Module.finrank ℂ (CuspForm (MTT.GammaOne 2) (k : ℤ)) := by
  have hd := gammaZero_binaryCoeffH1_dimension 2 (k - 2)
  rw [← gammaOne_two_eq_gammaZero_two] at hd
  have := hd.1
  have hw : ((k - 2 : ℕ) : ℤ) + 2 = k := by omega
  have hd' := hd.2
  rw [hw] at hd'
  exact (parabolicH1_finrank_le_binaryCoeffH1 2 (k - 2)).trans hd'.le

end MTT.Cohomology

theorem solution {k : ℕ} (hk : 2 ≤ k) :
    Module.finrank ℂ (MTT.Cohomology.ParabolicH1 2 (k - 2)) ≤
      2 * Module.finrank ℂ (CuspForm (MTT.GammaOne 2) (k : ℤ)) :=
  MTT.Cohomology.parabolicH1_finrank_le_level_two hk
