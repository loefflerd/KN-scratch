import Mathlib
import Definitions.FLT.Def_HeckeEis_BinaryFormRep
import Definitions.FLT.Def_Gamma0CoeffCohomology
import Definitions.FLT.Def_HeckeEis_EichlerIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold MatrixGroups ModularForm
theorem HeckeEis.IsEichlerIntegral.hasDerivAt_eval_iterate_pderiv {n : ℕ} {g : UpperHalfPlane → ℂ}
    {G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)} (hG : HeckeEis.IsEichlerIntegral n g G) {j : ℕ} (hj : j ≤ n)
    (τ : UpperHalfPlane) :
    HasDerivAt (fun z : ℂ => MvPolynomial.eval ![(1 : ℂ), -z]
        ((MvPolynomial.pderiv 1)^[j]
          ((G (UpperHalfPlane.ofComplex z) : ↥(HeckeEis.BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)))
      ((if j = n then ((n.factorial : ℕ) : ℂ) * g τ else 0)
        - MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)]
          ((MvPolynomial.pderiv 1)^[j + 1] ((G τ : ↥(HeckeEis.BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)))
      (τ : ℂ) := by sorry
