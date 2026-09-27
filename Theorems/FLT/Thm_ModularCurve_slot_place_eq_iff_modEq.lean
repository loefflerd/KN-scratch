import Definitions.FLT.Def_ModularCurve_PhiGen
import Definitions.FLT.Def_ModularCurve_QAdicPlace
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.LinearCombination

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve
theorem ModularCurve.slot_place_eq_iff_modEq (K : Type*) [Field K] [Algebra ℚ K] (N : ℕ) [NeZero N] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)
    (a b : ℕ) (ha : a ∣ N) [NeZero a] (a' b' : ℕ) (ha' : a' ∣ N) [NeZero a']
    (ι ι' : laurentBaseChange K (modularFunctionFieldFull N) →ₐ[K] LaurentSeries K)
    (hι₁ : ι ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩ =
        qExpand K N (coeffEmb K jq))
    (hι₂ : ι ⟨coeffEmb K (jqN N), coeffEmb_mem_laurentBaseChange K (jqd_mem_full N (dvd_refl N))⟩ =
        qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq)))
    (hι'₁ : ι' ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩ =
        qExpand K N (coeffEmb K jq))
    (hι'₂ : ι' ⟨coeffEmb K (jqN N), coeffEmb_mem_laurentBaseChange K (jqd_mem_full N (dvd_refl N))⟩ =
        qExpand K (a' * a') (qTwist (ζ ^ (b' * a')) (coeffEmb K jq)))
    (w w' : Place K (laurentBaseChange K (modularFunctionFieldFull N))) (γ γ' : ℤ)
    (hγ : 0 < γ) (hγ' : 0 < γ')
    (hw : ∀ x, w.ord x * γ = (ι x).order) (hw' : ∀ x, w'.ord x * γ' = (ι' x).order) :
    w = w' ↔ a = a' ∧ b ≡ b' [MOD Nat.gcd a (N / a)] := by sorry
