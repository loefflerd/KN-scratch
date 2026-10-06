module

public import Definitions.KN.Def_KN_SeededThetaConstructionV2B
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

section privateSection

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
end

end privateSection

public section publicSection

noncomputable section

/-- The rational prime `p` lies in the maximal ideal of the valuation ring of
`ℂ_p`. -/
theorem PadicComplexInt.natCast_prime_mem_maximalIdeal_v2
    (p : ℕ) [Fact p.Prime] :
    (p : 𝓞_ℂ_[p]) ∈ IsLocalRing.maximalIdeal (𝓞_ℂ_[p]) := _root_.solution p
end

end publicSection
