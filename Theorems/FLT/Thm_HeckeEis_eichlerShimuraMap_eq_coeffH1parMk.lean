import Definitions.FLT.Def_HeckeEis_EichlerIntegral

theorem HeckeEis.eichlerShimuraMap_eq_coeffH1parMk (n N : ℕ) (f : UpperHalfPlane → ℂ)
    {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hEI : HeckeEis.IsEichlerIntegral n f F)
    (hF : HeckeEis.IsEquivariantPrimitiveWith
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) F)
    (hpar : HeckeEis.IsParabolicCocycle
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) hF.cocycle) :
    HeckeEis.eichlerShimuraMap n N f
      = HeckeEis.coeffH1parMk _ ⟨hF.cocycle, ⟨hF.cocycle_mem_coeffCocycles, hpar⟩⟩ := by sorry
