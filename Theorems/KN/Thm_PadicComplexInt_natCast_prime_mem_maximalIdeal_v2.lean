import Definitions.KN.Def_KN_SeededThetaConstructionV2B
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

noncomputable section

/-- The rational prime `p` lies in the maximal ideal of the valuation ring of
`ℂ_p`. -/
theorem PadicComplexInt.natCast_prime_mem_maximalIdeal_v2
    (p : ℕ) [Fact p.Prime] :
    (p : 𝓞_ℂ_[p]) ∈ IsLocalRing.maximalIdeal (𝓞_ℂ_[p]) := by sorry
