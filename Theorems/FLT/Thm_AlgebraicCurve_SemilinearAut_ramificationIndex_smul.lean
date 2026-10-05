module

public import Definitions.FLT.Def_AlgebraicCurve_Correspondence

import Theorems.FLT.Thm_AlgebraicCurve_SemilinearAut_ord_algebraMap_smul
import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemilinearAut_ramificationIndex_smul

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} (hgg' : IntertwinesAlong (algebraMap F F') g g') (w : Place K F') : (g' • w).ramificationIndex F = w.ramificationIndex F := by
  unfold Place.ramificationIndex
  congr 1
  ext n
  simp only [Set.mem_ofPred_eq]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨f, hf, hford⟩
    exact ⟨g⁻¹ • f, by rwa [ne_eq, smul_eq_zero_iff_eq], by rw [← ord_algebraMap_smul hgg', hford]⟩
  · rintro ⟨f, hf, hford⟩
    refine ⟨g • f, by rwa [ne_eq, smul_eq_zero_iff_eq], ?_⟩
    rw [ord_algebraMap_smul hgg', inv_smul_smul, hford]

end

end S_AlgebraicCurve_SemilinearAut_ramificationIndex_smul
end P2MW
export P2MW.S_AlgebraicCurve_SemilinearAut_ramificationIndex_smul (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve AlgebraicCurve.SemilinearAut
theorem AlgebraicCurve.SemilinearAut.ramificationIndex_smul {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} (hgg' : IntertwinesAlong (algebraMap F F') g g') (w : Place K F') : (g' • w).ramificationIndex F = w.ramificationIndex F := _root_.P2MW.S_AlgebraicCurve_SemilinearAut_ramificationIndex_smul.solution hgg' w

end publicSection
