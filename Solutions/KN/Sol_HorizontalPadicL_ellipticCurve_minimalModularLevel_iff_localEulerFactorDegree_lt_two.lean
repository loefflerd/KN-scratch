import Theorems.KN.Thm_HorizontalPadicL_minimalModularLevel_dvd_iff_localEulerFactorDegreeBelowTwo
import Theorems.KN.Thm_HorizontalPadicL_not_minimalModularLevel_dvd_iff_localEulerFactorDegreeTwo
import Definitions.KN.Def_HorizontalPadicL_LocalEulerFactorDegree

set_option autoImplicit false
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
