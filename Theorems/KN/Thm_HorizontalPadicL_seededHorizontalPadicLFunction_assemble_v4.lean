import Definitions.KN.Def_KN_SeededHorizontalPadicLFunctionV3B
import Definitions.KN.Def_KN_SeededThetaConstructionV2B
import Definitions.KN.Def_KN_InverseSeedConventionV2

noncomputable section

namespace HorizontalPadicL

/-- Package a faithful normalized theta measure together with the original
positive-density prime system. -/
theorem seededHorizontalPadicLFunction_assemble_v4
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (hnew : IsNewEigenform f)
    (η : DirichletCharacterWithLevel) (ιp : MTT.Qbar →+* ℂ_[p])
    (L : SeededHorizontalPrimeSystemV3 p ιp f η B)
    (μ : SeededNormalizedThetaMeasureV3 L.toConstructionData)
    (hcharacters : μ.characters.HasExpectedProperties)
    (hinterp : μ.InterpolatesSeededCriticalValues)
    (htrivial : μ.measure.eval
      (trivialHorizontalCharacterV2 p L.toConstructionData.exponent) ≠ 0) :
    ∃ ν : SeededHorizontalPadicLFunctionV4 (B := B) p ιp f η,
      ν.primes = L ∧ ν.InterpolatesSeededCriticalValuesV4 ∧
      ν.measure.eval (trivialHorizontalCharacterV2 p ν.primes.exponent) ≠ 0 := by
  sorry

end HorizontalPadicL
