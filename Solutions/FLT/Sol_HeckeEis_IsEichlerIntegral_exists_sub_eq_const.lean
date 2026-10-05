import Definitions.FLT.Def_HeckeEis_EichlerIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

open UpperHalfPlane HeckeEis

theorem apply_eq_apply_of_hasDerivAt_zero {D : ℂ → ℂ}
    (hD : ∀ τ : ℍ, HasDerivAt D 0 ↑τ) (z w : ℍ) : D ↑z = D ↑w := by
  have hmem : ∀ σ : ℍ, (↑σ : ℂ) ∈ {c : ℂ | 0 < c.im} := fun σ => σ.2
  refine isOpen_upperHalfPlaneSet.is_const_of_fderiv_eq_zero
    ((convex_halfSpace_im_gt 0).isPreconnected)
    (fun x hx => ((hD ⟨x, hx⟩).differentiableAt).differentiableWithinAt)
    (fun x hx => ?_) (hmem z) (hmem w)
  have h0 := ((hD ⟨x, hx⟩).hasFDerivAt).fderiv
  rw [Pi.zero_apply, h0]
  ext1
  simp

theorem solution {n : ℕ} {f : UpperHalfPlane → ℂ}
    {F G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F) (hG : HeckeEis.IsEichlerIntegral n f G) :
    ∃ v : ↥(HeckeEis.BinaryForm ℂ n), ∀ τ : UpperHalfPlane, F τ - G τ = v := by
  refine ⟨F I - G I, fun τ => ?_⟩
  apply Subtype.ext
  rw [AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub]
  refine MvPolynomial.ext _ _ fun d => ?_
  rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply]
  have key : ∀ σ : ℍ, HasDerivAt
      (fun z : ℂ => AddMonoidAlgebra.coeff ((F (ofComplex z) : ↥(BinaryForm ℂ n)) :
          MvPolynomial (Fin 2) ℂ) d
        - AddMonoidAlgebra.coeff ((G (ofComplex z) : ↥(BinaryForm ℂ n)) :
          MvPolynomial (Fin 2) ℂ) d) 0 ↑σ :=
    fun σ => ((hF d σ).sub (hG d σ)).congr_deriv (sub_self _)
  have hc := apply_eq_apply_of_hasDerivAt_zero key τ I
  simpa only [ofComplex_apply] using hc
