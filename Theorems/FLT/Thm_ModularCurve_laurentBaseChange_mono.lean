module

public import Definitions.FLT.Def_ModularCurve_LaurentCoeff

import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_laurentBaseChange_mono

open ModularCurve IntermediateField HahnSeries

theorem solution (L : Type*) [Field L] [Algebra ℚ L] {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (h : F₀ ≤ F₁) : ModularCurve.laurentBaseChange L F₀ ≤ ModularCurve.laurentBaseChange L F₁ :=
  by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange L (h hy)

end S_ModularCurve_laurentBaseChange_mono
end P2MW
export P2MW.S_ModularCurve_laurentBaseChange_mono (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.laurentBaseChange_mono (L : Type*) [Field L] [Algebra ℚ L] {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (h : F₀ ≤ F₁) : ModularCurve.laurentBaseChange L F₀ ≤ ModularCurve.laurentBaseChange L F₁ := _root_.P2MW.S_ModularCurve_laurentBaseChange_mono.solution L h

end publicSection
