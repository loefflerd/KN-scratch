import Definitions.FLT.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
theorem AlgebraicCurve.Place.ord_sum_algebraMap_mul_le_ord_of_linearIndependent_of_constantFieldExtension
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [IsAlgClosed K'] [IsCurveOver K F] [IsCurveOver K' F']
    (lift : Place K F → Place K' F')
    (hlift_ord : ∀ (P : Place K F) (f : F), (lift P).ord (algebraMap F F' f) = P.ord f)
    (v : Place K F) {ι : Type*} (B : ι → K') (hB : LinearIndependent K B)
    (g : ι →₀ F) (hg : g ≠ 0) :
    (∑ j ∈ g.support, algebraMap K' F' (B j) * algebraMap F F' (g j)) ≠ 0 ∧
    ∀ j ∈ g.support,
      (lift v).ord (∑ j ∈ g.support, algebraMap K' F' (B j) * algebraMap F F' (g j)) ≤
        v.ord (g j) := by sorry
