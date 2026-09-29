import Definitions.KN.Def_MTT_EigenformCoefficientPrime
import Theorems.KN.Thm_MTT_Eigenform_coefficientPrime_isMaximal
import Theorems.KN.Thm_MTT_Eigenform_coefficientPrime_ne_bot
import Theorems.KN.Thm_MTT_numberField_coefficientField
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Norm

set_option autoImplicit false
noncomputable section

open NumberField

namespace MTT.Eigenform

/-- The residue ring of the coefficient field at the prime selected by a
`p`-adic embedding. -/
abbrev coefficientResidueField
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :=
  (𝓞 f.coefficientField) ⧸ f.coefficientPrime ιp

/-- The coefficient residue ring is a field. This is a derived structure,
not additional data attached to the eigenform. -/
noncomputable abbrev coefficientResidueFieldField
    {N k p : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    Field (f.coefficientResidueField ιp) := by
  letI : (f.coefficientPrime ιp).IsMaximal :=
    f.coefficientPrime_isMaximal hN hk ιp
  exact Ideal.Quotient.field (f.coefficientPrime ιp)

/-- The coefficient residue field is finite. This is a derived structure,
not additional data attached to the eigenform. -/
noncomputable abbrev coefficientResidueFieldFintype
    {N k p : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    Fintype (f.coefficientResidueField ιp) := by
  letI : NumberField f.coefficientField :=
    MTT.numberField_coefficientField hN hk ι f
  letI : Finite (f.coefficientResidueField ιp) :=
    Ring.HasFiniteQuotients.finiteQuotient
      (f.coefficientPrime_ne_bot ιp)
  exact Fintype.ofFinite _

end MTT.Eigenform
