module

public import Definitions.KN.Def_KN_EllipticCurveAttachedEigenform

section privateSection

noncomputable section

open HorizontalPadicL

namespace HorizontalPadicL

theorem attachedEigenformCandidate_isNew (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hmod : IsModular E) (hnormalized :
      CuspForm.IsNormalizedEigenform (modularFormAtConductor E hmod).form)
    (iota : MTT.Qbar →+* ℂ) :
    IsNewEigenform (attachedEigenformCandidate E hmod hnormalized iota) := by
  classical
  intro M hM hMN
  rintro ⟨g, hg⟩
  have hME : Nonempty (ModularFormAtLevel E M) := ⟨{
    level_pos := hM
    form := g
    coeff_eq := fun n => by
      rw [hg n]
      simp [attachedEigenformCandidate]
  }⟩
  exact (Nat.not_lt_of_ge (Nat.find_min' hmod hME)) hMN

end HorizontalPadicL

theorem solution
    (iota : MTT.Qbar →+* ℂ) (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hmod : IsModular E) :
    IsNewEigenform (attachedEigenform iota E hmod) := by
  exact attachedEigenformCandidate_isNew E hmod
    (ellipticCurve_attachedForm_isNormalizedEigenform E hmod) iota

end

end privateSection

public section publicSection

noncomputable section

open HorizontalPadicL

theorem HorizontalPadicL.attachedEigenform_isNew
    (iota : MTT.Qbar →+* ℂ) (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hmod : IsModular E) :
    IsNewEigenform (attachedEigenform iota E hmod) := _root_.solution iota E hmod

end

end publicSection
