import Definitions.KN.Def_KN_HorizontalPadicLAux

set_option autoImplicit false

namespace HorizontalPadicL

/-- A set of natural numbers having positive natural density relative to the
rational primes is infinite. -/
theorem positiveDensityPrimeSet_infinite_v2
    (A : Set ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hdensity : HasPrimeNaturalDensity A δ) : A.Infinite := by sorry

end HorizontalPadicL
