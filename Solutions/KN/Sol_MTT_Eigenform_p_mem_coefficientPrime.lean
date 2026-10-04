import Definitions.KN.Def_MTT_EigenformCoefficientPrime

noncomputable section

open NumberField

theorem solution
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    (p : 𝓞 f.coefficientField) ∈ f.coefficientPrime ιp := by
  rw [f.mem_coefficientPrime_iff ιp]
  have hp := Padic.norm_p_lt_one (p := p)
  have hext : ‖(p : ℂ_[p])‖ = ‖(p : ℚ_[p])‖ := by
    simpa using PadicComplex.norm_extends' p (p : ℚ_[p])
  simpa using hext.trans_lt hp
