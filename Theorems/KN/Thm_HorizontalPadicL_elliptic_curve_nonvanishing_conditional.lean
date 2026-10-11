module

public import Definitions.KN.Def_KN_EllipticCurveAttachedEigenform
public import Definitions.KN.Def_KN_QuadraticTwistSeed

import Theorems.KN.Thm_HorizontalPadicL_attachedEigenform_isNew
import Theorems.KN.Thm_HorizontalPadicL_attachedEigenform_nonvanishingCount_eq
import Theorems.KN.Thm_HorizontalPadicL_attachedEigenform_hasContinuousLocalFieldRepresentations
import Theorems.KN.Thm_HorizontalPadicL_corollary_5_17_of_quadratic_twist

public section publicSection

namespace HorizontalPadicL

/-- Elliptic-curve nonvanishing conditional on a quadratic-twist seed for the
specific eigenform attached to the curve. -/
theorem elliptic_curve_nonvanishing_of_quadratic_seed
    (ι : MTT.Qbar →+* ℂ) (E : WeierstrassCurve ℚ) [E.IsElliptic] (d : ℕ)
    (hmod : IsModular E) (hcase1 : d % 4 = 2 ∧ 6 ≤ d)
    (hSeed : HasQuadraticTwistSeed (attachedEigenform ι E hmod) d) :
    ∃ α : ℝ, 0 < α ∧
      HasLogPowerLowerBound (nonvanishingCount ι E hmod d) α := by
  let : (attachedEigenform ι E hmod).HasContinuousLocalFieldRepresentations :=
    attachedEigenform_hasContinuousLocalFieldRepresentations ι E hmod
  obtain ⟨η, hηprim, hηorder, hηcoprime, hηnonzero⟩ := hSeed
  obtain ⟨α, hα, hbound⟩ := corollary_5_17_of_quadratic_twist
    (modularConductor_pos E hmod) (by norm_num) (by norm_num)
    ι (attachedEigenform ι E hmod) (attachedEigenform_isNew ι E hmod)
    d hcase1 η hηprim hηorder hηcoprime hηnonzero
  refine ⟨α, hα, ?_⟩
  rw [← funext (attachedEigenform_nonvanishingCount_eq ι E hmod d)]
  exact hbound

end HorizontalPadicL

end publicSection
