import Mathlib
import Definitions.FLT.Def_AlgebraicCurve_Correspondence
import Definitions.FLT.Def_AlgebraicCurve_BaseChangeGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open scoped IntermediateField
theorem AlgebraicCurve.natCard_place_ord_sub_pos_le_natCard_doubleCoset
    (K : Type*) [Field K] [IsAlgClosed K] {L : Type*} [Field L] [Algebra K L]
    (t : L) (hfin : FiniteDimensional K⟮t⟯ L) (hgal : IsGalois K⟮t⟯ L)
    {Γ₀ : Type*} [Group Γ₀] (σ : Γ₀ →* (L ≃ₐ[K⟮t⟯] L)) (hσ : Function.Surjective σ)
    (Γ Kst : Subgroup Γ₀) [Γ.FiniteIndex]
    (E : IntermediateField K⟮t⟯ L) (hE : ∀ γ ∈ Γ, ∀ e : E, σ γ (e : L) = e)
    (c : K) (W : AlgebraicCurve.Place K L) (hW : 0 < W.ord (t - algebraMap K L c))
    (hD : ∀ k ∈ Kst, AlgebraicCurve.SemilinearAut.ofAlgAut ((σ k).restrictScalars K) • W = W)
    (x : E) (hx : (x : L) = t) :
    Nat.card {P : AlgebraicCurve.Place K E // 0 < P.ord (x - algebraMap K E c)} ≤
      Nat.card (DoubleCoset.Quotient (Γ : Set Γ₀) (Kst : Set Γ₀)) := by sorry
