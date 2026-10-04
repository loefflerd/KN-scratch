module

public import Definitions.FLT.Def_ModularCurve_X0
public import Mathlib.FieldTheory.Relrank

import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_relfinrank_modularFunctionField

namespace ModularCurve
p2m_export "ModularCurve" "qExpand jq jqN modularFunctionField adjoin_jq_le"
end ModularCurve
p2m_open_scoped "ModularCurve" in
open IntermediateField in
private theorem ModularCurve.relfinrank_modularFunctionField (N : ℕ) [NeZero N] :
    IntermediateField.relfinrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
      (modularFunctionField N) =
    Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
      (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
        ({jqN N} : Set (LaurentSeries ℚ))) := by
  have key : extendScalars (ModularCurve.adjoin_jq_le N) =
      adjoin (adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) ({jqN N} : Set (LaurentSeries ℚ)) := by
    have key0 := extendScalars_adjoin (ModularCurve.adjoin_jq_le N)
    refine key0.trans (le_antisymm ?_ ?_)
    · rw [adjoin_le_iff, Set.insert_subset_iff]
      refine ⟨?_, Set.singleton_subset_iff.mpr (subset_adjoin _ _ rfl)⟩
      exact (adjoin _ _).algebraMap_mem
        (⟨jq, subset_adjoin ℚ _ rfl⟩ : ↥(adjoin ℚ ({jq} : Set (LaurentSeries ℚ))))
    · exact adjoin.mono _ _ _ (Set.subset_insert _ _)
  rw [relfinrank_eq_finrank_of_le (ModularCurve.adjoin_jq_le N), key]

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_relfinrank_modularFunctionField.ModularCurve in

theorem solution (N : ℕ) [NeZero N] : IntermediateField.relfinrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (modularFunctionField N) = Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) ({jqN N} : Set (LaurentSeries ℚ))) :=
  ModularCurve.relfinrank_modularFunctionField N

end S_ModularCurve_relfinrank_modularFunctionField
end P2MW
export P2MW.S_ModularCurve_relfinrank_modularFunctionField (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.relfinrank_modularFunctionField (N : ℕ) [NeZero N] : IntermediateField.relfinrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (modularFunctionField N) = Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) ({jqN N} : Set (LaurentSeries ℚ))) := _root_.P2MW.S_ModularCurve_relfinrank_modularFunctionField.solution N

end publicSection
