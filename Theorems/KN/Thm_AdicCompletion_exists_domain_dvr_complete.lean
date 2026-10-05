module

public import Theorems.FLT.Thm_IsDiscreteValuationRing_adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete
public import Theorems.FLT.Thm_Ideal_IsMaximal_exists_adicCompletion_localization_ringEquiv
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.AdicCompletion.Topology

section privateSection

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

noncomputable section

open IsLocalRing

/-- Completing a Dedekind domain at a nonzero prime gives a complete DVR. -/
theorem solution
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : Ideal R) [P.IsPrime] (hP : P ≠ ⊥) :
    ∃ (_ : IsDomain (AdicCompletion P R))
      (_ : IsDiscreteValuationRing (AdicCompletion P R)),
      IsAdicComplete (maximalIdeal (AdicCompletion P R)) (AdicCompletion P R) := by
  let : P.IsMaximal := (inferInstance : P.IsPrime).isMaximal hP
  let A := Localization.AtPrime P
  let : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hP A
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨hD, hV, hC, _⟩ :=
    IsDiscreteValuationRing.adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete A ϖ hϖ
  obtain ⟨e, _⟩ := Ideal.IsMaximal.exists_adicCompletion_localization_ringEquiv P
  let : IsDomain (AdicCompletion P R) := e.symm.toMulEquiv.isDomain _
  let : IsDiscreteValuationRing (AdicCompletion P R) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  refine ⟨inferInstance, inferInstance, ?_⟩
  have hc := (IsAdicComplete.congr_ringEquiv
    (maximalIdeal (AdicCompletion (maximalIdeal A) A)) e).mpr hC
  rw [IsLocalRing.map_ringEquiv_maximalIdeal] at hc
  exact hc
end

end privateSection

public section publicSection

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

noncomputable section

open IsLocalRing

namespace AdicCompletion

/-- Completing a Dedekind domain at a nonzero prime gives a complete DVR. -/
theorem exists_domain_dvr_complete
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : Ideal R) [P.IsPrime] (hP : P ≠ ⊥) :
    ∃ (_ : IsDomain (AdicCompletion P R))
      (_ : IsDiscreteValuationRing (AdicCompletion P R)),
      IsAdicComplete (maximalIdeal (AdicCompletion P R)) (AdicCompletion P R) := _root_.solution P hP

end AdicCompletion
end

end publicSection
