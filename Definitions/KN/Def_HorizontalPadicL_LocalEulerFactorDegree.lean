module

public import Definitions.KN.Def_KN_HorizontalPadicL

@[expose] public section publicSection

namespace HorizontalPadicL

/-- Coefficient-side formulation that the local Euler polynomial of `E` at `p`
has degree strictly below two.  For an elliptic curve the reciprocal local Euler
factor then has the linear recurrence displayed here (including the degree-zero
case, when `E.LFunction p = 0`). -/
def LocalEulerFactorDegreeBelowTwo (E : WeierstrassCurve ℚ) (p : ℕ) : Prop :=
  ∀ r : ℕ,
    E.LFunction (p ^ (r + 2)) =
      E.LFunction p * E.LFunction (p ^ (r + 1))

/-- Coefficient-side formulation that the local Euler polynomial of `E` at `p`
has degree two, with its weight-two constant term equal to `p`. -/
def LocalEulerFactorDegreeTwo (E : WeierstrassCurve ℚ) (p : ℕ) : Prop :=
  ∀ r : ℕ,
    E.LFunction (p ^ (r + 2)) =
      E.LFunction p * E.LFunction (p ^ (r + 1)) -
        (p : ℤ) * E.LFunction (p ^ r)

end HorizontalPadicL

end publicSection
