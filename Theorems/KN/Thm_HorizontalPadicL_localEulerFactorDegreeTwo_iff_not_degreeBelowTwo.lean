import Definitions.KN.Def_HorizontalPadicL_LocalEulerFactorDegree

noncomputable section

namespace HorizontalPadicL

/-- The local Euler polynomial of an elliptic curve has degree at most two, so
having degree two is equivalent to not having degree strictly below two. In the
coefficient-side definitions used here, this identifies the normalized
quadratic recurrence with the negation of the subquadratic recurrence. -/
theorem localEulerFactorDegreeTwo_iff_not_degreeBelowTwo
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (p : ℕ) (hp : p.Prime) :
    LocalEulerFactorDegreeTwo E p ↔
      ¬ LocalEulerFactorDegreeBelowTwo E p := by
  sorry

end HorizontalPadicL
