import Definitions.FLT.Def_ModularCurve_PhiGen
import Definitions.FLT.Def_ModularCurve_QAdicPlace
import Definitions.FLT.Def_ModularCurve_AtkinLehner
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve
theorem ModularCurve.slot_ord_of_algHom_laurentBaseChange (K : Type*) [Field K] [Algebra ℚ K] (N : ℕ) [NeZero N] (ζ : Kˣ) (a b : ℕ) (ha : a ∣ N) [NeZero a]
    (ι : laurentBaseChange K (modularFunctionFieldFull N) →ₐ[K] LaurentSeries K)
    (hι₁ : ι ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩ =
        qExpand K N (coeffEmb K jq))
    (hι₂ : ι ⟨coeffEmb K (jqN N), coeffEmb_mem_laurentBaseChange K (jqd_mem_full N (dvd_refl N))⟩ =
        qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq)))
    (w : Place K (laurentBaseChange K (modularFunctionFieldFull N))) (γ : ℤ) (hγ : 0 < γ)
    (hw : ∀ x, w.ord x * γ = (ι x).order) :
    γ = a * Nat.gcd a (N / a) ∧
    w.ord ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_full N)⟩ =
        -((N / a / Nat.gcd a (N / a) : ℕ) : ℤ) ∧
    w.ord ⟨coeffEmb K (jqN N), coeffEmb_mem_laurentBaseChange K (jqd_mem_full N (dvd_refl N))⟩ =
        -((a / Nat.gcd a (N / a) : ℕ) : ℤ) := by sorry
