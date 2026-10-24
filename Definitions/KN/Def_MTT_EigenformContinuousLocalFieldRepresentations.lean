/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Definitions.KN.Def_KN_EigenformResidualGaloisRepresentationV2
public import Definitions.KN.Def_MTT_EigenformCoefficientLocalField
public import Definitions.FLT.Def_EllipticCurve_FrobeniusTrace
public import Definitions.FLT.Def_FLTPrelim_Ramification
public import Mathlib.FieldTheory.KrullTopology

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Continuous compatible local-field representations of an eigenform

This predicate records the representation-existence input to the KN development. It is an
assumption on an individual eigenform, not an unconditional existence theorem. For the eigenform
attached to an elliptic curve, the Tate-module construction supplies a proof of this predicate.

Extracted without changing its statement from the local conditional Corollary 5.17 development.
-/

@[expose] public noncomputable section publicSection

open NumberField

/-- The local-field Galois representations required by the conditional KN theorem.
This is an assumption on this eigenform, not an instance asserted for all eigenforms.
Representations are required at each prime and p-adic embedding used by the construction. -/
class MTT.Eigenform.HasContinuousLocalFieldRepresentations
    {N k : ℕ} {ι : MTT.Qbar →+* ℂ} (f : MTT.Eigenform N k ι) : Prop where
  exists_representation {p : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
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
                    (l : 𝓞 f.coefficientField) ^ (k - 1))))

end publicSection
