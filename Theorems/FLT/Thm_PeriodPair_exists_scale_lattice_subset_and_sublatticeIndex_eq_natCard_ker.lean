import Definitions.FLT.Def_PeriodPair_Uniformization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem PeriodPair.exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker
    (L L' : PeriodPair) (hL : L.DiscriminantNeZero) (hL' : L'.DiscriminantNeZero) (α : ℂˣ)
    (ψ : L.weierstrassCurve.toAffine.Point →+ L'.weierstrassCurve.toAffine.Point)
    (hψ : ∀ z : ℂ, L'.toPoint hL' ((α : ℂ) * z) = ψ (L.toPoint hL z)) :
    ∃ β : ℂˣ, ((L'.scale β).lattice : Set ℂ) ⊆ L.lattice ∧
      PeriodPair.sublatticeIndex L (L'.scale β) = Nat.card ψ.ker := by sorry
