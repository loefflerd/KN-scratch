import Definitions.FLT.Def_ModularCurve_PhiGen
import Definitions.FLT.Def_ModularCurve_QAdicPlace
import Definitions.FLT.Def_ModularCurve_AtkinLehner
import Definitions.FLT.Def_AlgebraicCurve_DivisorPushPull
import Definitions.FLT.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.FLT.Def_AlgebraicCurve_PlacesOverDVR
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Int.CardIntervalMod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve
theorem ModularCurve.exists_slot_of_isCusp (K : Type*) [Field K] [Algebra ℚ K] (N : ℕ) [NeZero N] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)
    (w : Place K (laurentBaseChange K (modularFunctionFieldFull N)))
    (hc : IsCusp (⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩ :
        laurentBaseChange K (modularFunctionFieldFull N)) w) :
    ∃ a b : ℕ, a ∣ N ∧ b < N / a ∧ Nat.gcd (Nat.gcd a b) (N / a) = 1 ∧
      ∃ (_ : NeZero a) (ι : laurentBaseChange K (modularFunctionFieldFull N) →ₐ[K] LaurentSeries K),
        ι ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩ =
            qExpand K N (coeffEmb K jq) ∧
        ι ⟨coeffEmb K (jqN N), coeffEmb_mem_laurentBaseChange K (jqd_mem_full N (dvd_refl N))⟩ =
            qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq)) ∧
        ∀ x, w.ord x * ((a * Nat.gcd a (N / a) : ℕ) : ℤ) = (ι x).order := by sorry
