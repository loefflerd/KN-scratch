import Mathlib
import Definitions.FLT.Def_PeriodPair_Uniformization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped UpperHalfPlane
theorem PeriodPair.jLattice_ofTau (τ : ℍ) :
    (PeriodPair.ofTau τ).jLattice = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ := by sorry
