import Definitions.KN.Def_KN_SeededThetaConstructionV2B
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

noncomputable section

/-- The rational prime `p` lies in the maximal ideal of the valuation ring of
`ℂ_p`. -/
theorem solution
    (p : ℕ) [Fact p.Prime] :
    (p : 𝓞_ℂ_[p]) ∈ IsLocalRing.maximalIdeal (𝓞_ℂ_[p]) := by
  rw [IsLocalRing.mem_maximalIdeal]
  change ¬ IsUnit (p : 𝓞_ℂ_[p])
  rw [(PadicComplexInt.integers p).isUnit_iff_valuation_eq_one]
  change Valued.v (p : ℂ_[p]) ≠ 1
  rw [PadicComplex.valuation_p]
  simpa [one_div, inv_eq_one] using (Fact.out : p.Prime).ne_one
