import Definitions.KN.Def_HorizontalPadicL_LocalEulerFactorDegree

set_option autoImplicit false

namespace HorizontalPadicL

theorem minimalModularLevel_dvd_iff_localEulerFactorDegreeBelowTwo
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (hmod : IsModular E)
    (p : ℕ) (hp : p.Prime) :
    (p ∣ modularConductor E hmod ↔ LocalEulerFactorDegreeBelowTwo E p) := by
  sorry

end HorizontalPadicL
