import Mathlib
import Definitions.FLT.Def_AdicCompletionLocalRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open IsLocalRing

theorem IsDiscreteValuationRing.adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete
    (C : Type u) [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] (ϖ : C) (hϖ : Irreducible ϖ) :
    ∃ (_ : IsDomain (AdicCompletion (IsLocalRing.maximalIdeal C) C))
      (_ : IsDiscreteValuationRing (AdicCompletion (IsLocalRing.maximalIdeal C) C))
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal C) C)) (AdicCompletion (IsLocalRing.maximalIdeal C) C)),
      Irreducible (algebraMap C (AdicCompletion (IsLocalRing.maximalIdeal C) C) ϖ) ∧
      (∀ (n : ℕ) (c : C), algebraMap C (AdicCompletion (IsLocalRing.maximalIdeal C) C) c ∈
          Ideal.span {algebraMap C (AdicCompletion (IsLocalRing.maximalIdeal C) C) ϖ ^ n} → c ∈ Ideal.span {ϖ ^ n}) ∧
      (∀ (n : ℕ) (w : AdicCompletion (IsLocalRing.maximalIdeal C) C), ∃ c : C,
          w - algebraMap C (AdicCompletion (IsLocalRing.maximalIdeal C) C) c ∈
            Ideal.span {algebraMap C (AdicCompletion (IsLocalRing.maximalIdeal C) C) ϖ ^ n}) := by sorry
