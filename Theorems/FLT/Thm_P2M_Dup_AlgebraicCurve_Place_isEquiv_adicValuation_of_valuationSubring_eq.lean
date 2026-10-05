module

public import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup
public import Definitions.FLT.Def_AlgebraicCurve_RatFuncPlaces

import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_isEquiv_adicValuation_of_valuationSubring_eq

open IsDedekindDomain WithZero IsLocalRing

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext heightOneSpectrum adicValuation toValuationSubring"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

p2m_export "AlgebraicCurve.Place" "adicValuation_valuationSubring"
private theorem rowMain {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] {w : Valuation F Γ}
    (h : w.valuationSubring = v.toValuationSubring) : w.IsEquiv v.adicValuation :=
  (Valuation.isEquiv_iff_valuationSubring _ _).mpr
    (h.trans v.adicValuation_valuationSubring.symm)

end Place

end AlgebraicCurve

end

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_isEquiv_adicValuation_of_valuationSubring_eq.AlgebraicCurve in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] {w : Valuation F Γ}
    (h : w.valuationSubring = v.toValuationSubring) :
    w.IsEquiv v.adicValuation :=
  AlgebraicCurve.Place.rowMain v h

end S_AlgebraicCurve_Place_isEquiv_adicValuation_of_valuationSubring_eq
end P2MW
export P2MW.S_AlgebraicCurve_Place_isEquiv_adicValuation_of_valuationSubring_eq (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
theorem P2M.Dup.AlgebraicCurve.Place.isEquiv_adicValuation_of_valuationSubring_eq {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] {w : Valuation F Γ}
    (h : w.valuationSubring = v.toValuationSubring) :
    w.IsEquiv v.adicValuation := _root_.P2MW.S_AlgebraicCurve_Place_isEquiv_adicValuation_of_valuationSubring_eq.solution v h

end publicSection
