module

public import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup
public import Definitions.FLT.Def_AlgebraicCurve_RatFuncPlaces

import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_ord_eq_zero_iff_adicValuation_eq_one

open IsDedekindDomain WithZero IsLocalRing

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "adicValuation adicValuation_ne_zero ord"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem rowMain {f : F} (hf : f ≠ 0) :
    v.ord f = 0 ↔ v.adicValuation f = 1 := by
  simp only [ord, neg_eq_zero]
  constructor
  · intro h
    have h2 := exp_log (v.adicValuation_ne_zero hf)
    rw [h, exp_zero] at h2
    exact h2.symm
  · intro h
    rw [h, log_one]

end Place

end AlgebraicCurve

end

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_ord_eq_zero_iff_adicValuation_eq_one.AlgebraicCurve in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F} (hf : f ≠ 0) :
    v.ord f = 0 ↔ v.adicValuation f = 1 :=
  AlgebraicCurve.Place.rowMain v hf

end S_AlgebraicCurve_Place_ord_eq_zero_iff_adicValuation_eq_one
end P2MW
export P2MW.S_AlgebraicCurve_Place_ord_eq_zero_iff_adicValuation_eq_one (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
theorem P2M.Dup.AlgebraicCurve.Place.ord_eq_zero_iff_adicValuation_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F} (hf : f ≠ 0) :
    v.ord f = 0 ↔ v.adicValuation f = 1 := _root_.P2MW.S_AlgebraicCurve_Place_ord_eq_zero_iff_adicValuation_eq_one.solution v hf

end publicSection
