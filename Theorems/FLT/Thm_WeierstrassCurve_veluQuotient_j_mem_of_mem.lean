import Definitions.FLT.Def_WeierstrassCurve_Velu

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem WeierstrassCurve.veluQuotient_j_mem_of_mem {F : Type*} [Field F] {S : Type*} [SetLike S F] [SubfieldClass S F]
    (W : WeierstrassCurve F) (K : S) (T : Finset (F × F))
    (h₁ : W.a₁ ∈ K) (h₂ : W.a₂ ∈ K) (h₃ : W.a₃ ∈ K) (h₄ : W.a₄ ∈ K) (h₆ : W.a₆ ∈ K)
    (hT : ∀ P ∈ T, P.1 ∈ K ∧ P.2 ∈ K) (hΔ : (W.veluQuotient T).Δ ≠ 0) :
    haveI : (W.veluQuotient T).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    (W.veluQuotient T).j ∈ K := by sorry
