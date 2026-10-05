module

public import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup
public import Definitions.FLT.Def_AlgebraicCurve_RatFuncPlaces

import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_ord_ofHeightOneSpectrum_ne_zero_iff

open IsDedekindDomain WithZero IsLocalRing

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ofHeightOneSpectrum"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext heightOneSpectrum adicValuation adicValuation_ne_zero ord ofHeightOneSpectrum toValuationSubring"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

p2m_export "AlgebraicCurve.Place" "adicValuation_valuationSubring"

p2m_export "AlgebraicCurve.Place" "isEquiv_adicValuation_of_valuationSubring_eq"

p2m_export "AlgebraicCurve.Place" "ord_eq_zero_iff_adicValuation_eq_one"
section OfHeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
  [Algebra K R] [IsScalarTower K R F]

private theorem isEquiv_adicValuation_ofHeightOneSpectrum (w : HeightOneSpectrum R) :
    (w.valuation F).IsEquiv (ofHeightOneSpectrum (K := K) w).adicValuation :=
  (ofHeightOneSpectrum (K := K) w).isEquiv_adicValuation_of_valuationSubring_eq rfl

private theorem rowMain (w : HeightOneSpectrum R) {q : R} (hq : q ≠ 0) :
    (ofHeightOneSpectrum (K := K) (F := F) w).ord (algebraMap R F q) ≠ 0 ↔ q ∈ w.asIdeal := by
  have hq' : algebraMap R F q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hq
  rw [ne_eq, (ofHeightOneSpectrum (K := K) w).ord_eq_zero_iff_adicValuation_eq_one hq',
    ← (isEquiv_adicValuation_ofHeightOneSpectrum (K := K) (F := F) w).eq_one_iff_eq_one,
    HeightOneSpectrum.valuation_eq_one_iff_notMem, not_not]

end OfHeightOneSpectrum

end Place

end AlgebraicCurve

end

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_ord_ofHeightOneSpectrum_ne_zero_iff.AlgebraicCurve in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
    [Algebra K R] [IsScalarTower K R F] (w : IsDedekindDomain.HeightOneSpectrum R) {q : R} (hq : q ≠ 0) :
    (Place.ofHeightOneSpectrum (K := K) (F := F) w).ord (algebraMap R F q) ≠ 0 ↔ q ∈ w.asIdeal :=
  AlgebraicCurve.Place.rowMain (K := K) (F := F) w hq

end S_AlgebraicCurve_Place_ord_ofHeightOneSpectrum_ne_zero_iff
end P2MW
export P2MW.S_AlgebraicCurve_Place_ord_ofHeightOneSpectrum_ne_zero_iff (solution)

end privateSection

public section publicSection

open AlgebraicCurve
theorem P2M.Dup.AlgebraicCurve.Place.ord_ofHeightOneSpectrum_ne_zero_iff {K F : Type*} [Field K]
    [Field F] [Algebra K F] {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F]
    [IsFractionRing R F] [Algebra K R] [IsScalarTower K R F]
    (w : IsDedekindDomain.HeightOneSpectrum R) {q : R} (hq : q ≠ 0) :
    (Place.ofHeightOneSpectrum (K := K) (F := F) w).ord (algebraMap R F q) ≠ 0 ↔ q ∈ w.asIdeal :=
  _root_.P2MW.S_AlgebraicCurve_Place_ord_ofHeightOneSpectrum_ne_zero_iff.solution w hq

end publicSection
