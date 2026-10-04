import Definitions.KN.Def_KN_PrimePowerPropagationV2
import Definitions.KN.Def_KN_InverseSeedConventionV2

noncomputable section
open scoped BigOperators

namespace HorizontalPadicL

/-- Congruence modulo p^m implies that the maximal local p-power quotient
has exponent at least m. -/
theorem SeededHorizontalPrimeSystemV3.orderExponent_le_exponent_v2
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeSystemV3 p ιp f η B) :
    ∀ n, L.orderExponent ≤ L.exponent n := by
  sorry

end HorizontalPadicL
