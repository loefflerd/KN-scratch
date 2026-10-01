import Definitions.FLT.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem CuspForm.heckeTLin_comm {N : ℕ} (k : ℤ) {p q : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (hq : q.Prime) (hqN : ¬ q ∣ N) :
    Commute (CuspForm.heckeTLin k hp hpN) (CuspForm.heckeTLin k hq hqN) := by sorry
