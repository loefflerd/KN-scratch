import Definitions.KN.Def_MTT_EigenformCoefficientField
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.RingTheory.Valuation.Integral

set_option autoImplicit false
noncomputable section

open NumberField

namespace MTT

/-- Restriction of a `p`-adic embedding to the integer ring of a subfield
of `Qbar`, with codomain the valuation ring of `ℂ_[p]`. -/
def ringOfIntegersToPadicComplexInt
    {p : ℕ} [Fact p.Prime] (K : Subfield Qbar)
    (ιp : Qbar →+* ℂ_[p]) : 𝓞 K →+* 𝓞_ℂ_[p] where
  toFun x := ⟨ιp (x : Qbar), by
    apply (PadicComplexInt.integers (p := p)).mem_of_integral
    apply IsIntegral.map_of_comp_eq
      (algebraMap ℤ (𝓞_ℂ_[p])) (ιp.comp K.subtype)
    · ext z
      simp
    · exact x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)

namespace Eigenform

/-- The prime of the coefficient field selected by a `p`-adic embedding.
It is the inverse image of the maximal ideal of the valuation ring of
`ℂ_[p]`. -/
def coefficientPrime
    {N k p : ℕ} {ι : Qbar →+* ℂ} [Fact p.Prime]
    (f : Eigenform N k ι) (ιp : Qbar →+* ℂ_[p]) :
    Ideal (𝓞 f.coefficientField) :=
  (IsLocalRing.maximalIdeal (𝓞_ℂ_[p])).comap
    (ringOfIntegersToPadicComplexInt f.coefficientField ιp)

/-- Membership in the coefficient prime is exactly strict `p`-adic
integrality. -/
theorem mem_coefficientPrime_iff
    {N k p : ℕ} {ι : Qbar →+* ℂ} [Fact p.Prime]
    (f : Eigenform N k ι) (ιp : Qbar →+* ℂ_[p])
    (x : 𝓞 f.coefficientField) :
    x ∈ f.coefficientPrime ιp ↔ ‖ιp ((x : f.coefficientField) : Qbar)‖ < 1 := by
  rw [coefficientPrime, Ideal.mem_comap]
  have hval := Valuation.mem_maximalIdeal_iff
    (v := (PadicComplex.valued p).v)
    (a := ringOfIntegersToPadicComplexInt f.coefficientField ιp x)
  change ringOfIntegersToPadicComplexInt f.coefficientField ιp x ∈
      IsLocalRing.maximalIdeal (𝓞_ℂ_[p]) ↔
    Valued.v (ιp ((x : f.coefficientField) : Qbar)) < 1 at hval
  rw [hval, PadicComplex.norm_eq_norm]
  simp only [Valuation.norm, PadicComplex.RankOne.hom_eq_embedding,
    Valuation.embedding_restrict]
  exact NNReal.coe_lt_one.symm

end Eigenform

end MTT
