import Definitions.KN.Def_KN_TruncatedHorizontalCoefficientsV2

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- Vanishing of the primitive cyclic Fourier frequencies forces a factor of `p`
in each coefficient of the marginal on the correcting coordinates. -/
theorem HorizontalMeasure.truncatedFiniteLevel_norm_le_of_primitive_twists_vanish_v2
    {p : ℕ} [Fact p.Prime] {e : ℕ → ℕ} {R : Subring ℂ_[p]}
    (μ : HorizontalMeasure R p e) (m : ℕ) (hm : 0 < m) (he : ∀ n, m ≤ e n)
    (A : Finset ℕ) (χ : HorizontalCharacter p e)
    (horder : orderOf χ.toMonoidHom = p ^ m) (hdisjoint : Disjoint χ.support A)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ y : HorizontalFiniteGroup p (fun _ ↦ m) (A ∪ χ.support),
      ‖(μ.truncatedFiniteLevel m he (A ∪ χ.support) y : ℂ_[p])‖ ≤ B)
    (hvanish : ∀ a : ℕ, a < p ^ m → Nat.Coprime a p →
      ∀ ξ : HorizontalCharacter p e, ξ.support ⊆ A →
        orderOf ξ.toMonoidHom ∣ p ^ m →
        μ.eval ((χ.powerOnSupport a).mulOnUnion ξ) = 0) :
    ∀ x : HorizontalFiniteGroup p (fun _ ↦ m) A,
      ‖(μ.truncatedFiniteLevel m he A x : ℂ_[p])‖ ≤ B / (p : ℝ) := by
  sorry

end HorizontalPadicL
