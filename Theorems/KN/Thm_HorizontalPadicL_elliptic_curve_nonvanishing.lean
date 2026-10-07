module

public import Definitions.KN.Def_KN_HorizontalPadicL

import Theorems.KN.Thm_HorizontalPadicL_corollary_5_17_v2
import Theorems.KN.Thm_HorizontalPadicL_ellipticCurve_eigenform_specialization_v2

section privateSection

open HorizontalPadicL

theorem solution
    (ι : MTT.Qbar →+* ℂ) (E : WeierstrassCurve ℚ) [E.IsElliptic] (d : ℕ)
    (hmod : IsModular E) (hcase1 : d % 4 = 2 ∧ 6 ≤ d) :
    ∃ α : ℝ, 0 < α ∧
      HasLogPowerLowerBound (nonvanishingCount ι E hmod d) α := by
  obtain ⟨f, hnew, hcount⟩ := ellipticCurve_eigenform_specialization_v2 ι E hmod
  obtain ⟨α, hα, hbound⟩ := corollary_5_17_v2
    (modularConductor_pos E hmod) (by norm_num) (by norm_num) ι f hnew d hcase1
  refine ⟨α, hα, ?_⟩
  rw [← funext (hcount d)]
  exact hbound

end privateSection

public section publicSection

open scoped BigOperators NNReal

namespace HorizontalPadicL

theorem elliptic_curve_nonvanishing
    (ι : MTT.Qbar →+* ℂ) (E : WeierstrassCurve ℚ) [E.IsElliptic] (d : ℕ)
    (hmod : IsModular E) (hcase1 : d % 4 = 2 ∧ 6 ≤ d) :
    ∃ α : ℝ, 0 < α ∧
      HasLogPowerLowerBound (nonvanishingCount ι E hmod d) α := _root_.solution ι E d hmod hcase1

end HorizontalPadicL

end publicSection
