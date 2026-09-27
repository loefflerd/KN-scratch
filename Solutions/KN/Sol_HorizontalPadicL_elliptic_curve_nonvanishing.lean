import Theorems.KN.Thm_HorizontalPadicL_corollary_5_17_v2
import Theorems.KN.Thm_HorizontalPadicL_ellipticCurve_eigenform_specialization_v2

set_option autoImplicit false

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
