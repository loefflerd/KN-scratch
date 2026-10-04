import Definitions.KN.Def_KN_PrimePowerPropagationV2

noncomputable section
open scoped BigOperators

namespace HorizontalPadicL

/-- There are only finitely many primitive algebraic Dirichlet characters
with conductor bounded by a fixed real number. Primitivity prevents duplicate
presentations at unbounded levels. -/
theorem primitiveCharacters_boundedConductor_finite_v2 (X : ℝ) :
    {χ : DirichletCharacterWithLevel |
      χ.2.IsPrimitive ∧ (χ.2.conductor : ℝ) ≤ X}.Finite := by
  sorry

end HorizontalPadicL
