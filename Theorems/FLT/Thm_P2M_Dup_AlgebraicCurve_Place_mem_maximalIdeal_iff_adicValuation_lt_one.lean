module

public import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup
public import Definitions.FLT.Def_AlgebraicCurve_RatFuncPlaces

import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_mem_maximalIdeal_iff_adicValuation_lt_one

open IsDedekindDomain WithZero IsLocalRing

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext heightOneSpectrum adicValuation adicValuation_coe_eq_one_iff toValuationSubring"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

p2m_export "AlgebraicCurve.Place" "adicValuation_valuationSubring"

p2m_export "AlgebraicCurve.Place" "mem_iff_adicValuation_le_one"
private theorem rowMain (a : v.toValuationSubring) :
    a ∈ IsLocalRing.maximalIdeal v.toValuationSubring ↔ v.adicValuation (a : F) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← v.adicValuation_coe_eq_one_iff,
    lt_iff_le_and_ne]
  have hle : v.adicValuation (a : F) ≤ 1 := v.mem_iff_adicValuation_le_one.mp a.2
  tauto

end Place

end AlgebraicCurve

end

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_mem_maximalIdeal_iff_adicValuation_lt_one.AlgebraicCurve in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (a : v.toValuationSubring) :
    a ∈ IsLocalRing.maximalIdeal v.toValuationSubring ↔ v.adicValuation (a : F) < 1 :=
  AlgebraicCurve.Place.rowMain v a

end S_AlgebraicCurve_Place_mem_maximalIdeal_iff_adicValuation_lt_one
end P2MW
export P2MW.S_AlgebraicCurve_Place_mem_maximalIdeal_iff_adicValuation_lt_one (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
theorem P2M.Dup.AlgebraicCurve.Place.mem_maximalIdeal_iff_adicValuation_lt_one {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (a : v.toValuationSubring) :
    a ∈ IsLocalRing.maximalIdeal v.toValuationSubring ↔ v.adicValuation (a : F) < 1 := _root_.P2MW.S_AlgebraicCurve_Place_mem_maximalIdeal_iff_adicValuation_lt_one.solution v a

end publicSection
