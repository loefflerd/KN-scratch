import Definitions.FLT.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped IntermediateField
theorem AlgebraicCurve.finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin
    {k : Type*} [Field k] [IsAlgClosed k] [CharZero k]
    {F : Type*} [Field F] [Algebra k F] [AlgebraicCurve.IsCurveOver k F]
    (y : F) (hy : Transcendental k y)
    [FiniteDimensional (IntermediateField.adjoin k ({y} : Set F)) F]
    {K' : Type*} [Field K'] [Algebra k K']
    {L : Type*} [Field L] [Algebra K' L] (t : L) (ht : Transcendental K' t)
    (E : IntermediateField (IntermediateField.adjoin K' ({t} : Set L)) L)
    [FiniteDimensional (IntermediateField.adjoin K' ({t} : Set L)) E]
    [Algebra F E] [Algebra k E] [IsScalarTower k K' E] [IsScalarTower k F E]
    (hyt : (algebraMap F E y : L) = t)
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F E)) = ⊤) :
    Module.finrank (IntermediateField.adjoin k ({y} : Set F)) F ≤
        Module.finrank (IntermediateField.adjoin K' ({t} : Set L)) E ∧
      ∀ u : F, u ≠ 0 →
        (Finite {P : AlgebraicCurve.Place K' E // 0 < P.ord (algebraMap F E u)} ∧
          Nat.card {P : AlgebraicCurve.Place K' E // 0 < P.ord (algebraMap F E u)} ≤
            Nat.card {P : AlgebraicCurve.Place k F // 0 < P.ord u}) ∧
        (Finite {P : AlgebraicCurve.Place K' E // P.ord (algebraMap F E u) < 0} ∧
          Nat.card {P : AlgebraicCurve.Place K' E // P.ord (algebraMap F E u) < 0} ≤
            Nat.card {P : AlgebraicCurve.Place k F // P.ord u < 0}) := by sorry
