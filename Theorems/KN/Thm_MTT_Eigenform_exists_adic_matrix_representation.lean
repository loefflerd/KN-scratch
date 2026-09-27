import Definitions.KN.Def_KN_EigenformResidualGaloisRepresentationV2
import Definitions.KN.Def_MTT_EigenformCoefficientCompletion
import Definitions.FLT.Def_GaloisRep_Residual

set_option autoImplicit false
noncomputable section

open NumberField

/-- Deligne's representation on a stable integral lattice at the chosen coefficient prime. -/
theorem MTT.Eigenform.exists_adic_matrix_representation
    {N k p : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (ιp : MTT.Qbar →+* ℂ_[p]) :
    ∃ ρ : (MTT.Qbar ≃ₐ[ℚ] MTT.Qbar) →*
        Matrix (Fin 2) (Fin 2) (f.coefficientCompletion ιp),
      (∀ n : ℕ, GaloisFactorsThroughFiniteLevel
        (((AdicCompletion.evalₐ (f.coefficientPrime ιp) n).toRingHom.mapMatrix
          (m := Fin 2)).toMonoidHom.comp ρ)) ∧
      (∀ (l : ℕ), l.Prime → Nat.Coprime l (N * p) →
        ∀ A : ValuationSubring MTT.Qbar, A.LiesOverPrime l →
          ∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
      (∀ (l : ℕ), l.Prime → Nat.Coprime l (N * p) →
        ∀ A : ValuationSubring MTT.Qbar, A.LiesOverPrime l →
          ∀ σ : MTT.Qbar ≃ₐ[ℚ] MTT.Qbar, A.IsFrobeniusAt σ l →
            Matrix.trace (ρ σ) =
              algebraMap (𝓞 f.coefficientField) (f.coefficientCompletion ιp)
                (f.integralCoeff hN hk l) ∧
            Matrix.det (ρ σ) =
              algebraMap (𝓞 f.coefficientField) (f.coefficientCompletion ιp)
                (f.integralNebentype (l : ZMod N) *
                  (l : 𝓞 f.coefficientField) ^ (k - 1))) := by
  sorry
