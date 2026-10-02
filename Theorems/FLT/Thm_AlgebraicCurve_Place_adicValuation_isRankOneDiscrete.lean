module

public import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup

section privateSection

open IsDedekindDomain WithZero IsLocalRing

noncomputable section

namespace AlgebraicCurve
open AlgebraicCurve

namespace Place
open AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem rowMain : v.adicValuation.IsRankOneDiscrete :=
  IsDiscreteValuationRing.isRankOneDiscrete v.toValuationSubring F

end Place

end AlgebraicCurve

end

open _root_.AlgebraicCurve in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.adicValuation.IsRankOneDiscrete :=
  AlgebraicCurve.Place.rowMain v

end privateSection

public section publicSection

open AlgebraicCurve
theorem AlgebraicCurve.Place.adicValuation_isRankOneDiscrete
    {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.adicValuation.IsRankOneDiscrete :=
  solution v

end publicSection
