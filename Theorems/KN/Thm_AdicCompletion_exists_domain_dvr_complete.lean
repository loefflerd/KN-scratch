import Theorems.FLT.Thm_IsDiscreteValuationRing_adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete
import Theorems.FLT.Thm_Ideal_IsMaximal_exists_adicCompletion_localization_ringEquiv
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.AdicCompletion.Topology

/-!
Completion of a Dedekind domain at a nonzero prime, by localization to a DVR.

Exact Prove2Me inputs:
* `IsDiscreteValuationRing.adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete`,
  theorem `a0e3aec5-3479-5c44-9927-bcd6e6f2d355`;
* `Ideal.IsMaximal.exists_adicCompletion_localization_ringEquiv`,
  theorem `d1ec29e0-26c9-5e94-b475-5ce731ee73ca`.

Mathlib supplies the DVR property of the localization and transfer of domain,
DVR, and adic completeness along the completion comparison.
-/

set_option autoImplicit false
noncomputable section

open IsLocalRing

namespace AdicCompletion

/-- Completing a Dedekind domain at a nonzero prime gives a complete DVR. -/
theorem exists_domain_dvr_complete
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : Ideal R) [P.IsPrime] (hP : P ≠ ⊥) :
    ∃ (_ : IsDomain (AdicCompletion P R))
      (_ : IsDiscreteValuationRing (AdicCompletion P R)),
      IsAdicComplete (maximalIdeal (AdicCompletion P R)) (AdicCompletion P R) := by
  sorry

end AdicCompletion
