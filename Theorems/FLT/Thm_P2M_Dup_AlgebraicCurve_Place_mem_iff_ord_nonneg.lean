module

public import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup
public import Definitions.FLT.Def_ModularCurve_CharLFrobeniusGeomLevel

import Definitions.FLT.Def_AlgebraicCurve_DivisorPushPull
import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_mem_iff_ord_nonneg

open IsDedekindDomain WithZero IsLocalRing

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ord ord_unit_smul_zpow exists_unit_mul_zpow toValuationSubring"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)


p2m_export "AlgebraicCurve.Place" "ord_nonneg_of_mem"

p2m_export "AlgebraicCurve.Place" "mem_of_ord_nonneg"
private theorem rowMain {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f :=
  ⟨v.ord_nonneg_of_mem, v.mem_of_ord_nonneg hf⟩

end Place

end AlgebraicCurve

end

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_mem_iff_ord_nonneg.AlgebraicCurve in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f :=
  AlgebraicCurve.Place.rowMain v hf

end S_AlgebraicCurve_Place_mem_iff_ord_nonneg
end P2MW
export P2MW.S_AlgebraicCurve_Place_mem_iff_ord_nonneg (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
theorem P2M.Dup.AlgebraicCurve.Place.mem_iff_ord_nonneg {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f := _root_.P2MW.S_AlgebraicCurve_Place_mem_iff_ord_nonneg.solution v hf

end publicSection
