import Definitions.FLT.Def_ModularForm_HeckeOperatorForms
import Theorems.FLT.Thm_ModularFormClass_heckeT_heckeU_comm
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeTLin_heckeULin_comm

theorem solution {N : ℕ} [NeZero N] (k : ℤ) {p q : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (hqN : q ∣ N) :
    Commute (CuspForm.heckeTLin k hp hpN) (CuspForm.heckeULin k hqN) := by
  rw [commute_iff_eq]; ext f τ
  simpa using congrFun (ModularFormClass.heckeT_heckeU_comm f (by simp)
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hpN (h.trans hqN))) τ

end S_CuspForm_heckeTLin_heckeULin_comm
end P2MW
export P2MW.S_CuspForm_heckeTLin_heckeULin_comm (solution)
