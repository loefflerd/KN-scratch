module

public import Definitions.FLT.Def_ModularCurve_X0

import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Squarefree
import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_le_dedekindPsi

open ModularCurve Finset

theorem solution (N : ℕ) (hN : N ≠ 0) : N ≤ dedekindPsi N := by
  rw [dedekindPsi]
  have h1 : (1 : ℕ) ∈ {d ∈ N.divisors | Squarefree d} :=
    Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr hN, squarefree_one⟩
  simpa using Finset.single_le_sum (f := fun d => N / d) (fun d _ => Nat.zero_le _) h1

end S_ModularCurve_le_dedekindPsi
end P2MW
export P2MW.S_ModularCurve_le_dedekindPsi (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.le_dedekindPsi (N : ℕ) (hN : N ≠ 0) : N ≤ dedekindPsi N := _root_.P2MW.S_ModularCurve_le_dedekindPsi.solution N hN

end publicSection
