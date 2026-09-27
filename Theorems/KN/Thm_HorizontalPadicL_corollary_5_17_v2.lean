import Definitions.KN.Def_KN_HorizontalPadicLAux

set_option autoImplicit false

namespace HorizontalPadicL

theorem corollary_5_17_v2
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (heven : Even k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) (hnew : IsNewEigenform f)
    (d : ℕ) (hcase1 : d % 4 = 2 ∧ 6 ≤ d) :
    ∃ α : ℝ, 0 < α ∧
      HasLogPowerLowerBound (eigenformNonvanishingCount ι f d) α := by sorry

end HorizontalPadicL
