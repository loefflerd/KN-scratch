import Theorems.KN.Thm_HorizontalPadicL_minimalModularLevel_dvd_iff_localEulerFactorDegreeBelowTwo
import Theorems.KN.Thm_HorizontalPadicL_localEulerFactorDegreeTwo_iff_not_degreeBelowTwo

set_option autoImplicit false
noncomputable section

open HorizontalPadicL

theorem solution
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (hmod : IsModular E)
    (p : ℕ) (hp : p.Prime) :
    (¬ p ∣ modularConductor E hmod ↔ LocalEulerFactorDegreeTwo E p) := by
  rw [localEulerFactorDegreeTwo_iff_not_degreeBelowTwo E p hp]
  exact not_congr
    (minimalModularLevel_dvd_iff_localEulerFactorDegreeBelowTwo E hmod p hp)
