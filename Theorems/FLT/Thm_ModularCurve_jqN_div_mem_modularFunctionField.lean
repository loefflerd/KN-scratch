import Definitions.FLT.Def_ModularCurve_PhiGen
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.jqN_div_mem_modularFunctionField (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] {K : Type*} [Field K] [Algebra ℚ K] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (M * p)) (htw : ∀ y : LaurentSeries K, Polynomial.eval y ((minpoly (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN M)).map (((coeffEmb K).comp (qExpand ℚ (M * p))).comp (algebraMap (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (LaurentSeries ℚ)))) = 0 → ∀ w : Kˣ, y = qExpand K (M * p * M) (qTwist w (coeffEmb K jq)) → w = 1) (hsp : ∀ y : LaurentSeries K, Polynomial.eval y ((minpoly (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN M)).map (((coeffEmb K).comp (qExpand ℚ (M * p))).comp (algebraMap (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (LaurentSeries ℚ)))) = 0 → y ≠ coeffEmb K (qExpand ℚ (M * p) (jqN (M * p * p)))) : jqN M ∈ modularFunctionField (M * p) := by sorry
