import Definitions.FLT.Def_AlgebraicCurve_Repartitions
import Definitions.FLT.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.isIntegral_and_isIntegral_of_mem_riemannRochSpace_weightFloor
    (K : Type*) [Field K] (F : IntermediateField K (LaurentSeries K))
    (y : ↥F) (hy : (y : LaurentSeries K) = ModularCurve.jqModC K)
    [FiniteDimensional ↥(IntermediateField.adjoin K ({y} : Set ↥F)) ↥F]
    [Algebra.IsSeparable ↥(IntermediateField.adjoin K ({y} : Set ↥F)) ↥F]
    (m : ℕ) (D : AlgebraicCurve.Divisor K ↥F)
    (hD : ∀ w : AlgebraicCurve.Place K ↥F,
      D w = (if 0 < w.ord y then (2 * (m : ℤ) * w.ord y) / 3 else 0)
          + (if 0 < w.ord (y - 1728) then ((m : ℤ) * w.ord (y - 1728)) / 2 else 0)
          + (if w.ord y < 0 then (m : ℤ) * w.ord y else 0))
    (G : ↥F) (hG : G ∈ AlgebraicCurve.riemannRochSpace D) :
    IsIntegral ↥(Algebra.adjoin K ({ModularCurve.jqModC K} : Set (LaurentSeries K)))
        ((G : LaurentSeries K) ^ 6 * ModularCurve.jqModC K ^ (4 * m) *
          (ModularCurve.jqModC K - algebraMap K (LaurentSeries K) 1728) ^ (3 * m)) ∧
      IsIntegral ↥(Algebra.adjoin K ({(ModularCurve.jqModC K)⁻¹} : Set (LaurentSeries K)))
        ((G : LaurentSeries K) ^ 2 * ModularCurve.jqModC K ^ m *
          (ModularCurve.jqModC K - algebraMap K (LaurentSeries K) 1728) ^ m) := by sorry
