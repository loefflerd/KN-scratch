module

public import Definitions.FLT.Def_HeckeEis_EichlerIntegral

section privateSection

open UpperHalfPlane HeckeEis
open scoped MatrixGroups

theorem solution
    {K : Type*} [CommRing K] {Γ : Subgroup SL(2, ℤ)} {V : Type*} [AddCommGroup V] [Module K V]
    {ρ : Representation K Γ V} {F G : UpperHalfPlane → V}
    (hF : HeckeEis.IsEquivariantPrimitiveWith ρ F) (hG : HeckeEis.IsEquivariantPrimitiveWith ρ G)
    {v : V} (h : ∀ τ : UpperHalfPlane, F τ - G τ = v) :
    hF.cocycle - hG.cocycle ∈ HeckeEis.coeffCoboundaries ρ := by
  rw [mem_coeffCoboundaries_iff]
  refine ⟨-v, funext fun γ => ?_⟩
  change ρ γ (-v) - -v = (F ((γ : SL(2, ℤ)) • I) - ρ γ (F I)) - (G ((γ : SL(2, ℤ)) • I) - ρ γ (G I))
  rw [map_neg, sub_eq_iff_eq_add.mp (h ((γ : SL(2, ℤ)) • I)), sub_eq_iff_eq_add.mp (h I), map_add]
  abel

end privateSection

public section publicSection

open scoped MatrixGroups
theorem HeckeEis.IsEquivariantPrimitiveWith.cocycle_sub_cocycle_mem_coeffCoboundaries
    {K : Type*} [CommRing K] {Γ : Subgroup SL(2, ℤ)} {V : Type*} [AddCommGroup V] [Module K V]
    {ρ : Representation K Γ V} {F G : UpperHalfPlane → V}
    (hF : HeckeEis.IsEquivariantPrimitiveWith ρ F) (hG : HeckeEis.IsEquivariantPrimitiveWith ρ G)
    {v : V} (h : ∀ τ : UpperHalfPlane, F τ - G τ = v) :
    hF.cocycle - hG.cocycle ∈ HeckeEis.coeffCoboundaries ρ := _root_.solution hF hG h

end publicSection
