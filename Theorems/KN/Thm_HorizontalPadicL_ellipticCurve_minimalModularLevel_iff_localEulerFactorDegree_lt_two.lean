module

public import Definitions.KN.Def_HorizontalPadicL_LocalEulerFactorDegree

import Theorems.KN.Thm_HorizontalPadicL_minimalModularLevel_dvd_iff_localEulerFactorDegreeBelowTwo
import Theorems.KN.Thm_HorizontalPadicL_not_minimalModularLevel_dvd_iff_localEulerFactorDegreeTwo

section privateSection

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option linter.all false

open HorizontalPadicL

theorem _root_.solution
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (hmod : IsModular E)
    (p : ℕ) (hp : p.Prime) :
    (p ∣ modularConductor E hmod ↔ LocalEulerFactorDegreeBelowTwo E p) ∧
      (¬ p ∣ modularConductor E hmod ↔ LocalEulerFactorDegreeTwo E p) :=
  ⟨HorizontalPadicL.minimalModularLevel_dvd_iff_localEulerFactorDegreeBelowTwo E hmod p hp,
   HorizontalPadicL.not_minimalModularLevel_dvd_iff_localEulerFactorDegreeTwo E hmod p hp⟩

end privateSection

public section publicSection

namespace HorizontalPadicL

/-- The prime support of the least modular level is exactly the set of places
where the elliptic curve's local Euler polynomial has degree below two;
equivalently, the primes outside the level are exactly those with the normalized
quadratic local factor. -/
theorem ellipticCurve_minimalModularLevel_iff_localEulerFactorDegree_lt_two
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (hmod : IsModular E)
    (p : ℕ) (hp : p.Prime) :
    (p ∣ modularConductor E hmod ↔ LocalEulerFactorDegreeBelowTwo E p) ∧
      (¬ p ∣ modularConductor E hmod ↔ LocalEulerFactorDegreeTwo E p) := _root_.solution E hmod p hp

end HorizontalPadicL

end publicSection
