import Definitions.FLT.Def_AlgebraicCurve_Differentials
import Definitions.FLT.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
theorem AlgebraicCurve.sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable
    (k : Type*) [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F]
    (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k ({x} : Set F)) F)
    (T : Finset (Place k F)) (hT : ∀ P ∈ T, 0 ≤ P.ord x)
    (Tinf : Finset (Place k F)) (hTinf : ∀ P ∈ Tinf, P.ord x < 0) :
    ∑ P ∈ T, P.ordDiff (KaehlerDifferential.D k F x) + ∑ P ∈ Tinf, (-P.ord x - 1) ≤
      2 * (genusFF k F : ℤ) - 2 +
        2 * (Module.finrank (IntermediateField.adjoin k ({x} : Set F)) F : ℤ) := by sorry
