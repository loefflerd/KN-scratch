import Definitions.FLT.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularForm.coeffHeckeT_comm (k : ℤ) {p q : ℕ} (hpq : Nat.Coprime p q) (a : ℕ → ℂ) : ModularForm.coeffHeckeT k p (ModularForm.coeffHeckeT k q a) = ModularForm.coeffHeckeT k q (ModularForm.coeffHeckeT k p a) := by sorry
