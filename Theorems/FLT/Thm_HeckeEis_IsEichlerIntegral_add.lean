module

public import Definitions.FLT.Def_HeckeEis_EichlerIntegral

import Mathlib.Analysis.Calculus.Deriv.Add

section privateSection

theorem solution {n : ℕ} {f g : UpperHalfPlane → ℂ} {F G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F) (hG : HeckeEis.IsEichlerIntegral n g G) :
    HeckeEis.IsEichlerIntegral n (f + g) (F + G) := by
  intro d τ
  have h := (hF d τ).add (hG d τ)
  simp only [← add_mul] at h
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.add_apply, Submodule.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]

end privateSection

public section publicSection

open scoped MatrixGroups
theorem HeckeEis.IsEichlerIntegral.add {n : ℕ} {f g : UpperHalfPlane → ℂ} {F G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F) (hG : HeckeEis.IsEichlerIntegral n g G) :
    HeckeEis.IsEichlerIntegral n (f + g) (F + G) := _root_.solution hF hG

end publicSection
