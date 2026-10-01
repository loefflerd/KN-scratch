import Definitions.FLT.Def_ModularCurve_CuspSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open OnePoint
theorem ModularCurve.ratPoint_eq_ratPoint_iff_of_isCoprime {a c a' c' : ℤ} (h : IsCoprime a c)
    (h' : IsCoprime a' c') :
    ModularCurve.ratPoint a c = ModularCurve.ratPoint a' c' ↔ (a = a' ∧ c = c') ∨ (a = -a' ∧ c = -c') := by sorry
