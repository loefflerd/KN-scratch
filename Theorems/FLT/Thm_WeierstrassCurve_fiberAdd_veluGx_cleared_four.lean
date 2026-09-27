import Definitions.FLT.Def_WeierstrassCurve_Velu

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem WeierstrassCurve.fiberAdd_veluGx_cleared_four {R : Type*} [CommRing R] (W : WeierstrassCurve R) (x y x₀ y₀ : R)
    (hP : W.toAffine.Equation x y) (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) :
    4 * (W.veluGx x y * (x - x₀) ^ 4 + (3 * ((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2) ^ 2 + 2 * W.a₂ * ((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2) * (x - x₀) ^ 2 + W.a₄ * (x - x₀) ^ 4 - W.a₁ * ((y - y₀) * (x * (x - x₀) ^ 2 - ((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2)) - y * (x - x₀) ^ 3 - W.a₁ * ((y - y₀) ^ 2 + W.a₁ * (y - y₀) * (x - x₀) - (W.a₂ + x + x₀) * (x - x₀) ^ 2) * (x - x₀) - W.a₃ * (x - x₀) ^ 3) * (x - x₀)))
      = 4 * (3 * (x * (x - x₀) ^ 2 + W.veluGx x₀ y₀ * (x - x₀)) ^ 2 + 2 * W.a₂ * (x * (x - x₀) ^ 2 + W.veluGx x₀ y₀ * (x - x₀)) * (x - x₀) ^ 2 + (W.a₄ - 5 * W.veluGx x₀ y₀) * (x - x₀) ^ 4 - W.a₁ * (y * (x - x₀) ^ 3 - W.veluGx x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀) * (x - x₀)) * (x - x₀)) := by sorry
