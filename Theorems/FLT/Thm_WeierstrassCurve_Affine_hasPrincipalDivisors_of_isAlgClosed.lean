import Mathlib
import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem WeierstrassCurve.Affine.hasPrincipalDivisors_of_isAlgClosed {F : Type*} [Field F] [IsAlgClosed F] (W : WeierstrassCurve.Affine F) [W.IsElliptic] : AlgebraicCurve.HasPrincipalDivisors F W.FunctionField := by sorry
