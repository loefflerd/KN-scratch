import Definitions.FLT.Def_AlgebraicCurve_RegularDifferentials
import Definitions.FLT.Def_ModularCurve_LevelNFunctionField

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
theorem ModularCurve.LevelN.exists_linearMap_regularDifferentials_cuspForm_injective
    (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring N) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring N) K]
    [IsFractionRing (ModularCurve.LevelN.ring N) K] :
    ∃ Φ : AlgebraicCurve.regularDifferentials ℂ K →ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma N) 2,
      Function.Injective Φ := by sorry
