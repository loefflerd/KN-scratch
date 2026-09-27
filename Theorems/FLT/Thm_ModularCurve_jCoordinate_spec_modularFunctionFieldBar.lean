import Definitions.FLT.Def_ModularCurve_AtkinLehner

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve
theorem ModularCurve.jCoordinate_spec_modularFunctionFieldBar (N : ℕ) [NeZero N] :
    (∀ (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        0 ≤ v.ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (L := AlgebraicClosure ℚ) (hx := jq_mem_full N)⟩ →
        ∃! c : AlgebraicClosure ℚ,
          0 < v.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (L := AlgebraicClosure ℚ) (hx := jq_mem_full N)⟩ -
            algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)) ∧
      (∀ c : AlgebraicClosure ℚ,
        {v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) |
          0 < v.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (L := AlgebraicClosure ℚ) (hx := jq_mem_full N)⟩ -
            algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)}.Finite) ∧
      ({v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) |
        v.ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (L := AlgebraicClosure ℚ) (hx := jq_mem_full N)⟩ < 0}.Finite) := by sorry
