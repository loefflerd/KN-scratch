module

public import Definitions.FLT.Def_ModularForm_HeckeOperatorForms

import Theorems.FLT.Thm_ModularFormClass_heckeT_heckeT_comm
import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeTLin_comm

theorem solution {N : ℕ} (k : ℤ) {p q : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (hq : q.Prime) (hqN : ¬ q ∣ N) :
    Commute (CuspForm.heckeTLin k hp hpN) (CuspForm.heckeTLin k hq hqN) := by
  by_cases hpq : p = q
  · subst hpq; exact Commute.refl _
  · rw [commute_iff_eq]; ext f τ
    simpa using congrFun (ModularFormClass.heckeT_heckeT_comm f (by simp)
      ((Nat.coprime_primes hp hq).mpr hpq)) τ

end S_CuspForm_heckeTLin_comm
end P2MW
export P2MW.S_CuspForm_heckeTLin_comm (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem CuspForm.heckeTLin_comm {N : ℕ} (k : ℤ) {p q : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (hq : q.Prime) (hqN : ¬ q ∣ N) :
    Commute (CuspForm.heckeTLin k hp hpN) (CuspForm.heckeTLin k hq hqN) := _root_.P2MW.S_CuspForm_heckeTLin_comm.solution k hp hpN hq hqN

end publicSection
