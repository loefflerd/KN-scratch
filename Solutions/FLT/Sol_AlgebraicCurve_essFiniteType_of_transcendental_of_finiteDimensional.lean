import Mathlib
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional

set_option autoImplicit false

open IntermediateField Polynomial

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    Algebra.EssFiniteType K F := by
  have := hfd
  let e : RatFunc K ≃ₐ[K] K⟮x⟯ := RatFunc.algEquivOfTranscendental x htr
  have : Algebra.EssFiniteType K[X] (RatFunc K) :=
    Algebra.EssFiniteType.of_isLocalization (RatFunc K) (nonZeroDivisors K[X])
  have : Algebra.EssFiniteType K (RatFunc K) := Algebra.EssFiniteType.comp K K[X] (RatFunc K)
  have : Algebra.EssFiniteType K ↥K⟮x⟯ := Algebra.EssFiniteType.of_surjective e.toAlgHom e.surjective
  have : Algebra.EssFiniteType ↥K⟮x⟯ F := Algebra.EssFiniteType.of_finiteType _ _
  exact Algebra.EssFiniteType.comp K ↥K⟮x⟯ F

end S_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
end P2MW
export P2MW.S_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional (solution)
