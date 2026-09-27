import Mathlib
import Definitions.FLT.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

universe u v w
theorem WeierstrassCurve.Affine.exists_algHom_functionField_baseChange_finrankAlong_eq
    {R₀ : Type u} [Field R₀] (W : WeierstrassCurve R₀) [W.IsElliptic]
    (F : Type v) [Field F] [Algebra R₀ F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (F' : Type w) [Field F'] [Algebra R₀ F'] [DecidableEq F'] [IsAlgClosed F'] [CharZero F']
    [Algebra F F'] [IsScalarTower R₀ F F']
    (ι : (W.baseChange F).toAffine.FunctionField →ₐ[F] (W.baseChange F).toAffine.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong F ι) :
    ∃ ι' : (W.baseChange F').toAffine.FunctionField →ₐ[F'] (W.baseChange F').toAffine.FunctionField,
      ι'.toRingHom.IsIntegral ∧ ∃ hfin' : FiniteAlong F' ι', finrankAlong F' ι' = finrankAlong F ι := by sorry
