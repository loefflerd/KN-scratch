import Definitions.KN.Def_KN_PrimePowerPropagationV2
import Definitions.KN.Def_KN_InverseSeedConventionV2

set_option autoImplicit false

namespace HorizontalPadicL

/-- Quantitative prime-power propagation from one faithful seeded horizontal
measure. The proof sketch separates Fourier theory, realization and counting. -/
theorem SeededHorizontalPadicLFunctionV4.primePower_propagation_v2
    {N k B p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (ν : SeededHorizontalPadicLFunctionV4 (B := B) p ιp f η)
    (hpodd : p ≠ 2) (m : ℕ) (hm : 0 < m)
    (hexponent : ν.primes.orderExponent = m)
    (hinterp : ν.InterpolatesSeededCriticalValuesV4)
    (htriv : ν.measure.eval
      (trivialHorizontalCharacterV2 p ν.primes.exponent) ≠ 0) :
    ∃ α : ℝ, 0 < α ∧
      HasLogPowerLowerBound
        (seededPrimePowerNonvanishingCount ι f η p m B) α := by
  sorry

end HorizontalPadicL
