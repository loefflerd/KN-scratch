import Mathlib.Analysis.Calculus.Deriv.Mul

import Definitions.FLT.Def_HeckeEis_EichlerIntegral

open UpperHalfPlane MvPolynomial CongruenceSubgroup

theorem solution {n : ℕ} {f : UpperHalfPlane → ℂ} {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F) (c : ℂ) :
    HeckeEis.IsEichlerIntegral n (c • f) (c • F) := by
  intro d τ
  have h := (hF d τ).const_mul c
  rw [← mul_assoc] at h
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.smul_apply, Submodule.coe_smul, coeff_smul, smul_eq_mul]
