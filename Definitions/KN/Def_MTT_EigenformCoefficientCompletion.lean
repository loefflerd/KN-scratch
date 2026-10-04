import Definitions.KN.Def_MTT_EigenformCoefficientResidueField
import Mathlib.RingTheory.AdicCompletion.Algebra

noncomputable section

open NumberField

namespace MTT.Eigenform

/-- The integral completion of the coefficient field at the chosen place. -/
abbrev coefficientCompletion
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :=
  AdicCompletion (f.coefficientPrime ιp) (𝓞 f.coefficientField)

/-- Reduction from the canonical integral completion to the canonical residue field. -/
def coefficientReduction
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    f.coefficientCompletion ιp →+* f.coefficientResidueField ιp :=
  (AdicCompletion.evalOneₐ (f.coefficientPrime ιp)).toRingHom

@[simp]
theorem coefficientReduction_algebraMap
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p])
    (x : 𝓞 f.coefficientField) :
    f.coefficientReduction ιp (algebraMap _ (f.coefficientCompletion ιp) x) =
      Ideal.Quotient.mk (f.coefficientPrime ιp) x := rfl

theorem coefficientReduction_surjective
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    Function.Surjective (f.coefficientReduction ιp) :=
  AdicCompletion.evalOneₐ_surjective (f.coefficientPrime ιp)

end MTT.Eigenform
