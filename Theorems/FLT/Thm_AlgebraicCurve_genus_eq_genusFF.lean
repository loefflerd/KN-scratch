module

public import Definitions.FLT.Def_AlgebraicCurve_RiemannRochRows

import Theorems.FLT.Thm_AlgebraicCurve_ell_canonicalDivisor_eq_genus_of_riemannRoch
import Theorems.FLT.Thm_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1
import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_genus_eq_genusFF

open AlgebraicCurve KaehlerDifferential

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates]
    (hRR : AlgebraicCurve.FunctionFieldRiemannRoch K F) (hWDA : AlgebraicCurve.WeilDualityAdelic K F)
    (hC : AlgebraicCurve.ConstantsAreBase K F) :
    AlgebraicCurve.genus K F = AlgebraicCurve.genusFF K F := by
  have : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[F⁄K])
  have h1 : (indexOfSpecialty (0 : Divisor K F) : ℤ) = (ell (canonicalDivisorOf hω - 0) : ℤ) := hWDA hω 0
  rw [sub_zero] at h1
  have h2 : (ell (canonicalDivisorOf hω) : ℤ) = (genus K F : ℤ) :=
    ell_canonicalDivisor_eq_genus_of_riemannRoch hRR hC hω
  have h3 : indexOfSpecialty (0 : Divisor K F) = Module.finrank K (H1 (0 : Divisor K F)) :=
    indexOfSpecialty_eq_finrank_H1 0
  have h4 : (indexOfSpecialty (0 : Divisor K F) : ℤ) = (genusFF K F : ℤ) := by
    rw [genusFF, ← h3]
  have : (genus K F : ℤ) = (genusFF K F : ℤ) := by
    rw [← h4, h1, h2]
  exact_mod_cast this

end S_AlgebraicCurve_genus_eq_genusFF
end P2MW
export P2MW.S_AlgebraicCurve_genus_eq_genusFF (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem AlgebraicCurve.genus_eq_genusFF
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates]
    (hRR : AlgebraicCurve.FunctionFieldRiemannRoch K F) (hWDA : AlgebraicCurve.WeilDualityAdelic K F)
    (hC : AlgebraicCurve.ConstantsAreBase K F) :
    AlgebraicCurve.genus K F = AlgebraicCurve.genusFF K F := _root_.P2MW.S_AlgebraicCurve_genus_eq_genusFF.solution hRR hWDA hC

end publicSection
