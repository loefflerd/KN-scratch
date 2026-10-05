import Definitions.FLT.Def_AlgebraicCurve_Differentials
import Theorems.FLT.Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero
import Theorems.FLT.Thm_AlgebraicCurve_isAlgebraic_adjoin_of_transcendental
import Theorems.FLT.Thm_KaehlerDifferential_span_D_eq_top_of_transcendental
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_ne_zero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"

noncomputable section
open KaehlerDifferential

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place.diffCoeff Place.diffCoeff_smul_D Place.ordDiff_def Place isAlgebraic_adjoin_of_transcendental"
namespace FF2R3
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
  [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]

include x in

private theorem isSeparable_adjoin (v : Place K F) {t : F} (ht : v.ord t ≠ 0) :
    Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F := by
  have : Algebra.IsAlgebraic (IntermediateField.adjoin K ({t} : Set F)) F :=
    AlgebraicCurve.isAlgebraic_adjoin_of_transcendental x (v.transcendental_of_ord_ne_zero ht)
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  infer_instance

include x in
theorem exists_eq_smul_D_of_ord_ne_zero (v : Place K F) {t : F} (ht : v.ord t ≠ 0) (ω : Ω[F⁄K]) :
    ∃ g : F, ω = g • D K F t := by
  have := isSeparable_adjoin x v ht
  have hspan := KaehlerDifferential.span_D_eq_top_of_transcendental K t (v.transcendental_of_ord_ne_zero ht)
  have hω : ω ∈ Submodule.span F {D K F t} := by rw [hspan]; trivial
  obtain ⟨g, hg⟩ := Submodule.mem_span_singleton.mp hω
  exact ⟨g, hg.symm⟩

include x in
theorem diffCoeff_smul_D_of_ord_ne_zero (v : Place K F) {t : F} (ht : v.ord t ≠ 0) (ω : Ω[F⁄K]) :
    Place.diffCoeff t ω • D K F t = ω :=
  Place.diffCoeff_smul_D (exists_eq_smul_D_of_ord_ne_zero x v ht ω)

end AlgebraicCurve.FF2R3

end

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {t : F} (ht : v.ord t ≠ 0) (ω : Ω[F⁄K]) :
    AlgebraicCurve.Place.diffCoeff t ω • KaehlerDifferential.D K F t = ω :=
  AlgebraicCurve.FF2R3.diffCoeff_smul_D_of_ord_ne_zero x v ht ω

end S_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_ne_zero
end P2MW
export P2MW.S_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_ne_zero (solution)
