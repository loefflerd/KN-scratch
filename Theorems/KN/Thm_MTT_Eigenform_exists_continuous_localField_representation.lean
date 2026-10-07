module

public import Definitions.KN.Def_KN_EigenformResidualGaloisRepresentationV2
public import Definitions.KN.Def_MTT_EigenformCoefficientLocalField
public import Definitions.FLT.Def_GaloisRep_Residual
public import Mathlib.FieldTheory.KrullTopology

public section publicSection

noncomputable section

open NumberField

/-- Deligne's characteristic-zero representation over the coefficient field
completed at the place selected by the p-adic embedding. The domain has the
Krull topology and the local field has its canonical discrete valuation topology. -/
theorem MTT.Eigenform.exists_continuous_localField_representation
    {N k p : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (ιp : MTT.Qbar →+* ℂ_[p]) :
    letI := f.coefficientCompletion_isDomain hN hk ιp
    letI := f.coefficientCompletion_isDiscreteValuationRing hN hk ιp
    letI := f.coefficientLocalFieldValued ιp
    ∃ ρ : (MTT.Qbar ≃ₐ[ℚ] MTT.Qbar) →*
        Matrix (Fin 2) (Fin 2) (f.coefficientLocalField ιp),
      Continuous ρ ∧
      (∀ (l : ℕ), l.Prime → Nat.Coprime l (N * p) →
        ∀ A : ValuationSubring MTT.Qbar, A.LiesOverPrime l →
          ∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
      (∀ (l : ℕ), l.Prime → Nat.Coprime l (N * p) →
        ∀ A : ValuationSubring MTT.Qbar, A.LiesOverPrime l →
          ∀ σ : MTT.Qbar ≃ₐ[ℚ] MTT.Qbar, A.IsFrobeniusAt σ l →
            Matrix.trace (ρ σ) =
              algebraMap (f.coefficientCompletion ιp) (f.coefficientLocalField ιp)
                (algebraMap (𝓞 f.coefficientField) (f.coefficientCompletion ιp)
                  (f.integralCoeff hN hk l)) ∧
            Matrix.det (ρ σ) =
              algebraMap (f.coefficientCompletion ιp) (f.coefficientLocalField ιp)
                (algebraMap (𝓞 f.coefficientField) (f.coefficientCompletion ιp)
                  (f.integralNebentype (l : ZMod N) *
                    (l : 𝓞 f.coefficientField) ^ (k - 1)))) := by
  sorry
end

end publicSection
