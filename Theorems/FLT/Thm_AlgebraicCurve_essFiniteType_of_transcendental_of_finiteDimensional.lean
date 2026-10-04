module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.EssentialFiniteness

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional

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

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {x : F} (htr : Transcendental K x)
    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    Algebra.EssFiniteType K F := _root_.P2MW.S_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional.solution htr hfd

end publicSection
