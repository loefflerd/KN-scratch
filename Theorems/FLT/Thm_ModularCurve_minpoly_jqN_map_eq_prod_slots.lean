import Definitions.FLT.Def_ModularCurve_PhiGen
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.minpoly_jqN_map_eq_prod_slots {K : Type*} [Field K] [Algebra ℚ K] (M : ℕ) [NeZero M] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) M) (hall : ∀ d : ℕ, d ∣ M → ∀ [NeZero d], Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) ({jqN d} : Set (LaurentSeries ℚ))) = dedekindPsi d ∧ modularFunctionField d = modularFunctionFieldFull d) : (minpoly (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN M)).map (((coeffEmb K).comp (qExpand ℚ M)).comp (algebraMap (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (LaurentSeries ℚ))) = ∏ a ∈ M.divisors, ∏ b ∈ (Finset.range (M / a)).filter (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1), (Polynomial.X - Polynomial.C (if h : a = 0 then 0 else letI : NeZero a := ⟨h⟩; qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq)))) := by sorry
