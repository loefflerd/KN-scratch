import Definitions.KN.Def_MTT_EigenformCoefficientField
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

set_option autoImplicit false
noncomputable section

/-- Every nebentype value, regarded as an element of the coefficient field,
belongs to its ring of integers. -/
theorem MTT.Eigenform.nebentype_mem_ringOfIntegers
    {N k : ℕ} {ι : MTT.Qbar →+* ℂ} (f : MTT.Eigenform N k ι)
    (a : ZMod N) :
    (⟨f.epsilon a, f.nebentype_mem_coefficientField a⟩ : f.coefficientField) ∈
      integralClosure ℤ f.coefficientField := by sorry
