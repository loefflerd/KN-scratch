import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open UpperHalfPlane in
open scoped Manifold in
theorem UpperHalfPlane.qExpansion_coeff_mul_width (f : UpperHalfPlane → ℂ) (h₀ : ℝ) (hh₀ : 0 < h₀)
    (hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) h₀)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f)
    (m' : ℕ) (hm' : 0 < m') (i : ℕ) :
    PowerSeries.coeff i (UpperHalfPlane.qExpansion ((m' : ℝ) * h₀) f) =
      if m' ∣ i then PowerSeries.coeff (i / m') (UpperHalfPlane.qExpansion h₀ f) else 0 := by sorry
