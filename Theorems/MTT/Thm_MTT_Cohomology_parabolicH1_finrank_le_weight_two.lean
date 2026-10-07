module

public import Definitions.MTT.Def_MTT_ParabolicCohomology
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import Definitions.FLT.Def_ModularCurve_PeriodMap
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination
import Theorems.FLT.Thm_ModularCurve_Period_exists_basis_parabolicHoms_of_isAddTorsionFree
import Theorems.FLT.Thm_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup

section privateSection

/-! # From degree-zero MTT cocycles to scalar parabolic homomorphisms

The comparison uses only the definitions: degree-zero homogeneous polynomials
are constants, and an integral determinant-one matrix of trace squared four
fixes a rational cusp. No period-map injectivity is used.
-/

noncomputable section

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

theorem degreeZero_eq_constant (N : ℕ) (P : gammaOneRep N 0) :
    P.val = MvPolynomial.C (AddMonoidAlgebra.coeff P.val 0) :=
  (MvPolynomial.homogeneousComponent_eq_self P.property).symm.trans
    (MvPolynomial.homogeneousComponent_zero P.val)

theorem degreeZero_action (N : ℕ) (g : CongruenceSubgroup.Gamma1 N)
    (P : gammaOneRep N 0) : (gammaOneRep N 0).ρ g P = P := by
  apply Subtype.ext
  change act g.val.val P.val = P.val
  rw [degreeZero_eq_constant N P]
  exact MvPolynomial.bind₁_C_right _ _

def degreeZeroCocycleHom (N : ℕ) (c : parabolicCocycles N 0) :
    Additive (CongruenceSubgroup.Gamma1 N) →+ ℂ where
  toFun g := AddMonoidAlgebra.coeff (c.val (Additive.toMul g)).val 0
  map_zero' := by
    have hc := groupCohomology.cocycles₁_map_one ⟨c.val, c.property.1⟩
    change c.val 1 = 0 at hc
    change AddMonoidAlgebra.coeff (c.val 1).val 0 = 0
    rw [hc]
    rfl
  map_add' g h := by
    change AddMonoidAlgebra.coeff (c.val (Additive.toMul g * Additive.toMul h)).val 0 = _
    rw [((mem_parabolicCocycles_iff _).mp c.property).1, degreeZero_action]
    change AddMonoidAlgebra.coeff ((c.val (Additive.toMul h)).val +
      (c.val (Additive.toMul g)).val) 0 = _
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, add_comm]

theorem degreeZeroCocycleHom_parabolic (N : ℕ) (c : parabolicCocycles N 0) :
    ModularCurve.Period.IsParabolicHom (CongruenceSubgroup.Gamma1 N)
      (degreeZeroCocycleHom N c) := by
  intro g hg
  obtain ⟨x, hx⟩ := exists_cusp_fixed_of_trace_sq g.val hg
  obtain ⟨P, hP⟩ := ((mem_parabolicCocycles_iff _).mp c.property).2 x g hx
  have hc : c.val g = 0 := by simpa only [degreeZero_action, sub_self] using hP
  change AddMonoidAlgebra.coeff (c.val g).val 0 = 0
  rw [hc]
  rfl

def degreeZeroToScalarParabolic (N : ℕ) : parabolicCocycles N 0 →ₗ[ℂ]
    ModularCurve.Period.parabolicHoms ℂ (CongruenceSubgroup.Gamma1 N) ℂ where
  toFun c := ⟨degreeZeroCocycleHom N c, degreeZeroCocycleHom_parabolic N c⟩
  map_add' c d := by
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro g
    exact DFunLike.congr_fun (AddMonoidAlgebra.coeff_add _ _) 0
  map_smul' a c := by
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro g
    exact MvPolynomial.coeff_smul 0 a _

theorem degreeZeroToScalarParabolic_injective (N : ℕ) :
    Function.Injective (degreeZeroToScalarParabolic N) := by
  intro c d h
  apply Subtype.ext
  funext g
  apply Subtype.ext
  rw [degreeZero_eq_constant N (c.val g), degreeZero_eq_constant N (d.val g)]
  congr 1
  exact congrArg (fun f => f.val (Additive.ofMul g)) h

theorem parabolicH1_degree_zero_finrank_le_scalar (N : ℕ)
    [FiniteDimensional ℂ
      (ModularCurve.Period.parabolicHoms ℂ (CongruenceSubgroup.Gamma1 N) ℂ)] :
    Module.finrank ℂ (ParabolicH1 N 0) ≤
      Module.finrank ℂ
        (ModularCurve.Period.parabolicHoms ℂ (CongruenceSubgroup.Gamma1 N) ℂ) := by
  have := FiniteDimensional.of_injective _ (degreeZeroToScalarParabolic_injective N)
  exact (Submodule.finrank_quotient_le _).trans
    (LinearMap.finrank_le_finrank_of_injective (degreeZeroToScalarParabolic_injective N))

end MTT.Cohomology

/-! # The MTT parabolic dimension bound in weight two at every positive level

The two imported theorems are already proved platform results, respectively
4b95a52a-d74a-57d1-ba7d-5f43023fa729 and
0ecd14cb-bbeb-5b1a-98cb-394f76c9069f. The new comparison with MTT's
polynomial-valued cohomology is proved in `WeightTwoScalarBridge`.
-/

section

namespace MTT.Cohomology

theorem parabolicH1_finrank_le_weight_two' {N : ℕ} (hN : 0 < N) :
    Module.finrank ℂ (ParabolicH1 N 0) ≤
      2 * Module.finrank ℂ (CuspForm (MTT.GammaOne N) 2) := by
  have : NeZero N := ⟨Nat.ne_of_gt hN⟩
  obtain ⟨r, bZ, hb⟩ :=
    ModularCurve.Period.exists_basis_parabolicHoms_of_isAddTorsionFree
      (CongruenceSubgroup.Gamma1 N)
  obtain ⟨bC, _⟩ := hb ℂ
  have := Module.Finite.of_basis bC
  have hr : Module.finrank ℂ
      (ModularCurve.Period.parabolicHoms ℂ (CongruenceSubgroup.Gamma1 N) ℂ) =
      Module.finrank ℤ
        (ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma1 N) ℤ) := by
    rw [Module.finrank_eq_card_basis bC, Module.finrank_eq_card_basis bZ]
  exact (parabolicH1_degree_zero_finrank_le_scalar N).trans (hr ▸
    ModularCurve.finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup
      (CongruenceSubgroup.Gamma1 N) (CongruenceSubgroup.Gamma1_is_congruence N))

end MTT.Cohomology

theorem solution {N : ℕ} (hN : 0 < N) :
    Module.finrank ℂ (MTT.Cohomology.ParabolicH1 N 0) ≤
      2 * Module.finrank ℂ (CuspForm (MTT.GammaOne N) 2) :=
  MTT.Cohomology.parabolicH1_finrank_le_weight_two' hN
end
end

end privateSection

public section publicSection

noncomputable section

theorem MTT.Cohomology.parabolicH1_finrank_le_weight_two {N : ℕ} (hN : 0 < N) :
    Module.finrank ℂ (MTT.Cohomology.ParabolicH1 N 0) ≤
      2 * Module.finrank ℂ (CuspForm (MTT.GammaOne N) 2) := _root_.solution hN
end

end publicSection
