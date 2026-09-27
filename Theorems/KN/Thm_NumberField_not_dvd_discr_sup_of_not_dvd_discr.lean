import Definitions.MTT.Def_MTT_Arithmetic
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

set_option autoImplicit false
noncomputable section

/-- If a rational prime is unramified in two number fields embedded in a
common algebraic closure, then it is unramified in their compositum. -/
theorem NumberField.not_dvd_discr_sup_of_not_dvd_discr
    (K₁ K₂ : IntermediateField ℚ MTT.Qbar)
    [NumberField K₁] [NumberField K₂]
    {l : ℤ} (hl : Prime l)
    (h₁ : ¬ l ∣ NumberField.discr K₁)
    (h₂ : ¬ l ∣ NumberField.discr K₂) :
    letI : NumberField ↥(K₁ ⊔ K₂) :=
      { to_charZero := inferInstance
        to_finiteDimensional := IntermediateField.finiteDimensional_sup K₁ K₂ }
    ¬ l ∣ NumberField.discr ↥(K₁ ⊔ K₂) := by sorry
