module

public import Definitions.FLT.Def_HeckeEis_EichlerIntegral

import Theorems.FLT.Thm_HeckeEis_IsEichlerIntegral_exists_sub_eq_const
import Theorems.FLT.Thm_HeckeEis_IsEquivariantPrimitiveWith_cocycle_sub_cocycle_mem_coeffCoboundaries

section privateSection

noncomputable section

namespace HeckeEis

open UpperHalfPlane CongruenceSubgroup

theorem SolMain.eqmk (n N : ℕ) (f : ℍ → ℂ) {F : ℍ → ↥(BinaryForm ℂ n)}
    (hEI : IsEichlerIntegral n f F)
    (hF : IsEquivariantPrimitiveWith ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) F)
    (hpar : IsParabolicCocycle ((binaryFormRepSL ℂ n).comp (Gamma0 N).subtype) hF.cocycle) :
    eichlerShimuraMap n N f
      = coeffH1parMk _ ⟨hF.cocycle, ⟨hF.cocycle_mem_coeffCocycles, hpar⟩⟩ := by
  obtain ⟨F₀, hEI₀, h₀, hpar₀, heq⟩ := eichlerShimuraMap_def n N f hEI hF hpar
  rw [heq, ← sub_eq_zero, ← map_sub, coeffH1parMk_eq_zero_iff]
  obtain ⟨v, hv⟩ := hEI₀.exists_sub_eq_const hEI
  exact h₀.cocycle_sub_cocycle_mem_coeffCoboundaries hF hv

end HeckeEis

end

theorem solution (n N : ℕ) (f : UpperHalfPlane → ℂ)
    {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hEI : HeckeEis.IsEichlerIntegral n f F)
    (hF : HeckeEis.IsEquivariantPrimitiveWith
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) F)
    (hpar : HeckeEis.IsParabolicCocycle
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) hF.cocycle) :
    HeckeEis.eichlerShimuraMap n N f
      = HeckeEis.coeffH1parMk _ ⟨hF.cocycle, ⟨hF.cocycle_mem_coeffCocycles, hpar⟩⟩ :=
  HeckeEis.SolMain.eqmk n N f hEI hF hpar

end privateSection

public section publicSection

theorem HeckeEis.eichlerShimuraMap_eq_coeffH1parMk (n N : ℕ) (f : UpperHalfPlane → ℂ)
    {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hEI : HeckeEis.IsEichlerIntegral n f F)
    (hF : HeckeEis.IsEquivariantPrimitiveWith
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) F)
    (hpar : HeckeEis.IsParabolicCocycle
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) hF.cocycle) :
    HeckeEis.eichlerShimuraMap n N f
      = HeckeEis.coeffH1parMk _ ⟨hF.cocycle, ⟨hF.cocycle_mem_coeffCocycles, hpar⟩⟩ := _root_.solution n N f hEI hF hpar

end publicSection
