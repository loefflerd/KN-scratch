import Definitions.KN.Def_KN_InverseSeedConventionV2

noncomputable section

namespace HorizontalPadicL

/-- The finite theta element has the expected critical-value zero set for
horizontal characters whose primitive conductor uses every prime in their
chosen support.  Characters with redundant support are treated separately by
the horizontal norm relations. -/
def SeededFiniteThetaDataV3.HasFullSupportCriticalZeroSetV2
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (Θ : SeededFiniteThetaDataV3 L) : Prop :=
  ∀ χ, (Θ.characters.realized χ).2.conductor = L.supportModulus χ.support →
    (Θ.eval χ ≠ 0 ↔
      let θ := primitiveProductV2 η (Θ.characters.realized χ)
      @MTT.criticalLValue ι f.form θ.1.1 ⟨Nat.ne_of_gt θ.1.2⟩ θ.2
        (k / 2 - 1) ≠ 0)

end HorizontalPadicL
