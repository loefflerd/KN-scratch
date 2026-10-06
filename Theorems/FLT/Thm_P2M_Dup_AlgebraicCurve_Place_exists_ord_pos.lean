module

public import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup
public import Definitions.FLT.Def_ModularCurve_CharLFrobeniusGeomLevel

import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_exists_ord_pos

open IsDedekindDomain WithZero IsLocalRing

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ord ord_coe_irreducible toValuationSubring"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem rowMain : ∃ f : F, f ≠ 0 ∧ 0 < v.ord f := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  refine ⟨(π : F), ?_, ?_⟩
  · simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  · rw [v.ord_coe_irreducible hπ]
    exact one_pos

end Place

end AlgebraicCurve

end

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_exists_ord_pos.AlgebraicCurve in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    ∃ f : F, f ≠ 0 ∧ 0 < v.ord f :=
  AlgebraicCurve.Place.rowMain v

end S_AlgebraicCurve_Place_exists_ord_pos
end P2MW
export P2MW.S_AlgebraicCurve_Place_exists_ord_pos (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
theorem P2M.Dup.AlgebraicCurve.Place.exists_ord_pos {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    ∃ f : F, f ≠ 0 ∧ 0 < v.ord f := _root_.P2MW.S_AlgebraicCurve_Place_exists_ord_pos.solution v

end publicSection
