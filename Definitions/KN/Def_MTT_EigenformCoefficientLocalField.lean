import Definitions.KN.Def_MTT_EigenformCoefficientCompletion
import Theorems.KN.Thm_AdicCompletion_exists_domain_dvr_complete
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
The canonical coefficient local field and its valuation. The coefficient
completion's domain, DVR, and completeness structures specialize the generic
prime-adic completion theorem without changing its existing ring structure.
-/

set_option autoImplicit false
noncomputable section

open NumberField IsLocalRing

namespace MTT.Eigenform

/-- The canonical coefficient completion is an integral domain. -/
theorem coefficientCompletion_isDomain
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (hN : 0 < N) (hk : 2 ≤ k)
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    IsDomain (f.coefficientCompletion ιp) := by
  let : NumberField f.coefficientField := MTT.numberField_coefficientField hN hk ι f
  let : (f.coefficientPrime ιp).IsMaximal := f.coefficientPrime_isMaximal hN hk ιp
  exact (AdicCompletion.exists_domain_dvr_complete
    (f.coefficientPrime ιp) (f.coefficientPrime_ne_bot ιp)).choose

/-- Its DVR structure uses the standard ring structure on the completion. -/
theorem coefficientCompletion_isDiscreteValuationRing
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (hN : 0 < N) (hk : 2 ≤ k)
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p])
    [IsDomain (f.coefficientCompletion ιp)] :
    IsDiscreteValuationRing (f.coefficientCompletion ιp) := by
  let : NumberField f.coefficientField := MTT.numberField_coefficientField hN hk ι f
  let : (f.coefficientPrime ιp).IsMaximal := f.coefficientPrime_isMaximal hN hk ιp
  obtain ⟨_, hV, _⟩ := AdicCompletion.exists_domain_dvr_complete
    (f.coefficientPrime ιp) (f.coefficientPrime_ne_bot ιp)
  exact hV

/-- The canonical coefficient completion is complete for its maximal ideal. -/
theorem coefficientCompletion_isAdicComplete
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (hN : 0 < N) (hk : 2 ≤ k)
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p])
    [IsDomain (f.coefficientCompletion ιp)]
    [IsDiscreteValuationRing (f.coefficientCompletion ιp)] :
    IsAdicComplete (maximalIdeal (f.coefficientCompletion ιp))
      (f.coefficientCompletion ιp) := by
  let : NumberField f.coefficientField := MTT.numberField_coefficientField hN hk ι f
  let : (f.coefficientPrime ιp).IsMaximal := f.coefficientPrime_isMaximal hN hk ιp
  obtain ⟨_, _, hC⟩ := AdicCompletion.exists_domain_dvr_complete
    (f.coefficientPrime ιp) (f.coefficientPrime_ne_bot ιp)
  exact hC

/-- The local coefficient field is the fraction field of the canonical
integral coefficient completion. -/
abbrev coefficientLocalField
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :=
  FractionRing (f.coefficientCompletion ιp)

/-- The normalized discrete valuation and its induced topology on the local
coefficient field. This definition uses the existing fraction-field structure. -/
@[instance_reducible]
noncomputable def coefficientLocalFieldValued
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p])
    [IsDomain (f.coefficientCompletion ιp)]
    [IsDiscreteValuationRing (f.coefficientCompletion ιp)] :
    Valued (f.coefficientLocalField ιp) (WithZero (Multiplicative ℤ)) :=
  Valued.mk' ((IsDiscreteValuationRing.maximalIdeal (f.coefficientCompletion ιp)).valuation
    (f.coefficientLocalField ιp))

end MTT.Eigenform
