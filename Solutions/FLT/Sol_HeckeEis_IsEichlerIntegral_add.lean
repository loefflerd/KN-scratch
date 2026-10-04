import Mathlib
import Definitions.FLT.Def_HeckeEis_BinaryFormRep
import Definitions.FLT.Def_Gamma0CoeffCohomology
import Definitions.FLT.Def_HeckeEis_EichlerIntegral
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_IsEichlerIntegral_add

set_option autoImplicit false

noncomputable section

namespace HeckeEis
p2m_export "HeckeEis" "BinaryForm IsEichlerIntegral"
p2m_open "HeckeEis"

open UpperHalfPlane MvPolynomial CongruenceSubgroup
open scoped MatrixGroups ModularForm

namespace SolMain

private theorem _root_.HeckeEis.SolMain.add {n : ℕ} {f g : ℍ → ℂ} {F G : ℍ → ↥(BinaryForm ℂ n)}
    (hF : IsEichlerIntegral n f F) (hG : IsEichlerIntegral n g G) :
    IsEichlerIntegral n (f + g) (F + G) := by
  intro d τ
  have h := (hF d τ).add (hG d τ)
  simp only [← add_mul] at h
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.add_apply, Submodule.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]

end SolMain
p2m_export "HeckeEis" "SolMain.add"
end HeckeEis

end

open scoped MatrixGroups ModularForm in
theorem solution {n : ℕ} {f g : UpperHalfPlane → ℂ} {F G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F) (hG : HeckeEis.IsEichlerIntegral n g G) :
    HeckeEis.IsEichlerIntegral n (f + g) (F + G) :=
  HeckeEis.SolMain.add hF hG

end S_HeckeEis_IsEichlerIntegral_add
end P2MW
export P2MW.S_HeckeEis_IsEichlerIntegral_add (solution)
