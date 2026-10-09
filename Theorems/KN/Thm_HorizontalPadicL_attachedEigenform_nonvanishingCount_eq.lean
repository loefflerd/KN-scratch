module

public import Definitions.KN.Def_KN_EllipticCurveAttachedEigenform

section privateSection

noncomputable section

open HorizontalPadicL

theorem solution
    (iota : MTT.Qbar →+* ℂ) (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hmod : IsModular E) :
    ∀ d : ℕ, ∀ X : ℝ,
      eigenformNonvanishingCount iota (attachedEigenform iota E hmod) d X =
        nonvanishingCount iota E hmod d X := by
  intro d X
  rfl
end

end privateSection

public section publicSection

noncomputable section

open HorizontalPadicL

theorem HorizontalPadicL.attachedEigenform_nonvanishingCount_eq
    (iota : MTT.Qbar →+* ℂ) (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hmod : IsModular E) :
    ∀ d : ℕ, ∀ X : ℝ,
      eigenformNonvanishingCount iota (attachedEigenform iota E hmod) d X =
        nonvanishingCount iota E hmod d X := _root_.solution iota E hmod
end

end publicSection
