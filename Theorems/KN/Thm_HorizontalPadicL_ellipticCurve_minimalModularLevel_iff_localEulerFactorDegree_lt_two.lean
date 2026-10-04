import Definitions.KN.Def_HorizontalPadicL_LocalEulerFactorDegree

namespace HorizontalPadicL

/-- The prime support of the least modular level is exactly the set of places
where the elliptic curve's local Euler polynomial has degree below two;
equivalently, the primes outside the level are exactly those with the normalized
quadratic local factor. -/
theorem ellipticCurve_minimalModularLevel_iff_localEulerFactorDegree_lt_two
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (hmod : IsModular E)
    (p : ℕ) (hp : p.Prime) :
    (p ∣ modularConductor E hmod ↔ LocalEulerFactorDegreeBelowTwo E p) ∧
      (¬ p ∣ modularConductor E hmod ↔ LocalEulerFactorDegreeTwo E p) := by
  sorry

end HorizontalPadicL
