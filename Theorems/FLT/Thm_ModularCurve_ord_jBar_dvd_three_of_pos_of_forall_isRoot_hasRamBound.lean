import Definitions.FLT.Def_ModularCurve_LaurentCoeff
import Definitions.FLT.Def_ModularCurve_QAdicPlace
import Definitions.FLT.Def_HahnSeries_RamificationBound

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open HahnSeries Polynomial ModularCurve
theorem ModularCurve.ord_jBar_dvd_three_of_pos_of_forall_isRoot_hasRamBound (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N)
    (htrio : ∀ r : HahnSeries ℚ (AlgebraicClosure ℚ),
      (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ)))
        (HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ)))).IsRoot r →
      HahnSeries.HasRamBound 3 r)
    (v : AlgebraicCurve.Place (AlgebraicClosure ℚ)
      ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))
    (hv : 0 < v.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))) :
    v.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) ∣ (3 : ℤ) := by sorry
