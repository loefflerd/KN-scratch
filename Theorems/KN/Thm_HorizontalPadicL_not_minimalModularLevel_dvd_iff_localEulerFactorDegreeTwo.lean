import Definitions.KN.Def_HorizontalPadicL_LocalEulerFactorDegree

set_option autoImplicit false

namespace HorizontalPadicL

theorem not_minimalModularLevel_dvd_iff_localEulerFactorDegreeTwo
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (hmod : IsModular E)
    (p : ℕ) (hp : p.Prime) :
    (¬ p ∣ modularConductor E hmod ↔ LocalEulerFactorDegreeTwo E p) := by
  sorry

end HorizontalPadicL
