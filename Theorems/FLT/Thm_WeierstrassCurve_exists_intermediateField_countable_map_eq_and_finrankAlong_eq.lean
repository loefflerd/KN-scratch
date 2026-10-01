import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.SimpleRing.Principal

import Definitions.FLT.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

universe u
theorem WeierstrassCurve.exists_intermediateField_countable_map_eq_and_finrankAlong_eq
    {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (E : WeierstrassCurve K) [E.IsElliptic]
    (ι : E.toAffine.FunctionField →ₐ[K] E.toAffine.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong K ι) :
    ∃ (K₀ : IntermediateField ℚ K), Countable K₀ ∧
      ∃ (E₀ : WeierstrassCurve K₀), E₀.IsElliptic ∧ E₀.map (algebraMap K₀ K) = E ∧
        ∃ (ι₀ : (E₀.baseChange (AlgebraicClosure K₀)).toAffine.FunctionField →ₐ[AlgebraicClosure K₀]
            (E₀.baseChange (AlgebraicClosure K₀)).toAffine.FunctionField),
          ι₀.toRingHom.IsIntegral ∧
          ∃ (hfin₀ : FiniteAlong (AlgebraicClosure K₀) ι₀),
            finrankAlong (AlgebraicClosure K₀) ι₀ = finrankAlong K ι := by sorry
