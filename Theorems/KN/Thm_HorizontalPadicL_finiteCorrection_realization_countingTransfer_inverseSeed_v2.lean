import Definitions.KN.Def_KN_PrimePowerPropagationV2
import Definitions.KN.Def_KN_InverseSeedConventionV2

noncomputable section
open scoped BigOperators

namespace HorizontalPadicL

/-- Faithful realization and interpolation turn finite Fourier corrections
into a bounded-fibre map on primitive Dirichlet characters. Represent the input
on its actual conductor support, disjoint from A. A prime-to-p power preserves
exact order; correction characters supported on A cannot cancel it.
For a fixed output, there are at most phi(p^m) choices of the power and finitely
many corrections on A. Conductor growth is bounded by the product of primes
indexed by A. This step needs no prime-density assumption. -/
theorem finiteCorrection_realization_countingTransfer_inverseSeed_v2
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeDataV3 p ιp f η B)
    (R : SeededHorizontalCharacterRealizationV3 L)
    (hR : R.HasExpectedProperties)
    {C : Subring ℂ_[p]} (μ : HorizontalMeasure C p L.exponent)
    (hpodd : p ≠ 2) (m : ℕ) (hm : 0 < m)
    (hinterp : ∀ χ,
      μ.eval χ ≠ 0 ↔
        let θ := primitiveProductV2 η (R.realized χ)
        @MTT.criticalLValue ι f.form θ.1.1 ⟨Nat.ne_of_gt θ.1.2⟩ θ.2
          (k / 2 - 1) ≠ 0)
    (A : Finset ℕ) (hcorr : μ.HasFiniteCorrection m A) :
    Nonempty (CharacterCountingTransfer
      (supportedPrimePowerCharacters L.primeAt A p m)
      (seededPrimePowerTwists ι f η p m B)) := by
  sorry

end HorizontalPadicL
