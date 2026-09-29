import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Manifold
theorem UpperHalfPlane.isBoundedAtImInfty_of_hasDerivAt_of_periodic {h : ℝ} (hh : 0 < h) {u v : UpperHalfPlane → ℂ}
    (hu_per : Function.Periodic (u ∘ UpperHalfPlane.ofComplex) h) (hu_hol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u)
    (hu_bdd : UpperHalfPlane.IsBoundedAtImInfty u)
    (hv : ∀ τ : UpperHalfPlane, HasDerivAt (v ∘ UpperHalfPlane.ofComplex) (u τ) ↑τ)
    (hv_per : Function.Periodic (v ∘ UpperHalfPlane.ofComplex) h) :
    UpperHalfPlane.IsBoundedAtImInfty v := by sorry
