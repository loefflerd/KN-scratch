import Definitions.KN.Def_KN_HorizontalPadicLAux

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

theorem ellipticCurve_eigenform_specialization_v2
    (iota : MTT.Qbar →+* ℂ) (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hmod : IsModular E) :
    ∃ f : MTT.Eigenform (modularConductor E hmod) 2 iota,
      IsNewEigenform f ∧
      ∀ d : ℕ, ∀ X : ℝ,
        eigenformNonvanishingCount iota f d X = nonvanishingCount iota E hmod d X := by sorry

end HorizontalPadicL
