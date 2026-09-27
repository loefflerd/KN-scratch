import Definitions.KN.Def_KN_HorizontalPadicL

set_option autoImplicit false

open scoped BigOperators NNReal

namespace HorizontalPadicL

theorem elliptic_curve_nonvanishing
    (ι : MTT.Qbar →+* ℂ) (E : WeierstrassCurve ℚ) [E.IsElliptic] (d : ℕ)
    (hmod : IsModular E) (hcase1 : d % 4 = 2 ∧ 6 ≤ d) :
    ∃ α : ℝ, 0 < α ∧
      HasLogPowerLowerBound (nonvanishingCount ι E hmod d) α := by sorry

end HorizontalPadicL
