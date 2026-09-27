import Definitions.FLT.Def_ModularCurve_PhiGen
import Definitions.FLT.Def_ModularCurve_QAdicPlace
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve
theorem ModularCurve.exists_algHom_laurentBaseChange_slot (K : Type*) [Field K] [Algebra ℚ K] (N : ℕ) [NeZero N] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)
    (a b : ℕ) (ha : a ∣ N) (hb : b < N / a) (hg : Nat.gcd (Nat.gcd a b) (N / a) = 1) [NeZero a] :
    ∃ ι : laurentBaseChange K (modularFunctionFieldFull N) →ₐ[K] LaurentSeries K,
      ι ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩ =
          qExpand K N (coeffEmb K jq) ∧
      ι ⟨coeffEmb K (jqN N), coeffEmb_mem_laurentBaseChange K (jqd_mem_full N (dvd_refl N))⟩ =
          qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq)) := by sorry
