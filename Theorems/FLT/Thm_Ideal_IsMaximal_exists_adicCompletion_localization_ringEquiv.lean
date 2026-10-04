import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Localization.AtPrime.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem Ideal.IsMaximal.exists_adicCompletion_localization_ringEquiv
    {C : Type u} [CommRing C] (𝔪 : Ideal C) [𝔪.IsMaximal] :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪)) (Localization.AtPrime 𝔪) ≃+*
        AdicCompletion 𝔪 C,
      ∀ c : C, e (algebraMap (Localization.AtPrime 𝔪) _ (algebraMap C (Localization.AtPrime 𝔪) c)) =
        algebraMap C (AdicCompletion 𝔪 C) c := by sorry
