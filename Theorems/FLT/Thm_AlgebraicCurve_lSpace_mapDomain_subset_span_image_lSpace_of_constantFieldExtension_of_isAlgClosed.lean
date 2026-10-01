import Definitions.FLT.Def_AlgebraicCurve_AdelicIndex
import Definitions.FLT.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem AlgebraicCurve.lSpace_mapDomain_subset_span_image_lSpace_of_constantFieldExtension_of_isAlgClosed
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [IsAlgClosed K'] [IsCurveOver K F] [IsCurveOver K' F']
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (lift : Place K F → Place K' F')
    (hlift_ord : ∀ (P : Place K F) (f : F), (lift P).ord (algebraMap F F' f) = P.ord f)
    (hlift_inj : Function.Injective lift)
    (D : Divisor K F) {f' : F'}
    (hf' : f' ∈ LSpace (K := K') (Finsupp.mapDomain lift D)) :
    f' ∈ Submodule.span K' ((algebraMap F F') '' (LSpace (K := K) D : Set F)) := by sorry
