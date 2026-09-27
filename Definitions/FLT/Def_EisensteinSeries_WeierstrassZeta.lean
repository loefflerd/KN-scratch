import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace EisensteinSeries

noncomputable def weierstrassZeta (τ : UpperHalfPlane) (z : ℂ) : ℂ :=
  1 / z + ∑' v : Fin 2 → ℤ, if v = 0 then 0 else
    (1 / (z - ((v 0 : ℂ) * τ + v 1)) + 1 / ((v 0 : ℂ) * τ + v 1) + z / ((v 0 : ℂ) * τ + v 1) ^ 2)

noncomputable def eisensteinG1 (N : ℕ) (v : Fin 2 → ℤ) (τ : UpperHalfPlane) : ℂ :=
  1 / (N : ℂ) *
    (weierstrassZeta τ (((v 0 : ℂ) * τ + v 1) / N) -
      ((v 0 : ℂ) * ((τ : ℂ) * G2 τ - 2 * Real.pi * Complex.I) + (v 1 : ℂ) * G2 τ) / N)

end EisensteinSeries

