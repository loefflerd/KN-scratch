import Definitions.KN.Def_KN_PrimePowerPropagationV2

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HorizontalPadicL

/-- A map with uniformly bounded finite fibres and bounded conductor growth
preserves logarithmic-power lower bounds. Explicit finiteness assumptions
prevent Set.ncard of an infinite set from silently becoming zero. -/
theorem CharacterCountingTransfer.logLowerBound_v2
    {S T : Set DirichletCharacterWithLevel}
    (F : CharacterCountingTransfer S T)
    (hS : ∀ X : ℝ, {χ | χ ∈ S ∧ (χ.2.conductor : ℝ) ≤ X}.Finite)
    (hT : ∀ X : ℝ, {χ | χ ∈ T ∧ (χ.2.conductor : ℝ) ≤ X}.Finite)
    (α : ℝ) (hα : 0 < α)
    (hcount : HasLogPowerLowerBound (characterConductorCount S) α) :
    HasLogPowerLowerBound (characterConductorCount T) α := by
  sorry

end HorizontalPadicL
