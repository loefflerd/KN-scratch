import Definitions.FLT.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.dedekindPsi_prime_pow (p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) : dedekindPsi (p ^ k) = p ^ k + p ^ (k - 1) := by sorry
