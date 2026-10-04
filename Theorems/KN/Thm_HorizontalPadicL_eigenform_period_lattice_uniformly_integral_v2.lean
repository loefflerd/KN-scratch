import Definitions.KN.Def_KN_SeededThetaConstructionV2B

noncomputable section

namespace HorizontalPadicL

/-- Finite generation of the integral period lattice gives one scalar clearing
all `p`-adic denominators of the normalized signed modular symbols. -/
theorem eigenform_period_lattice_uniformly_integral_v2
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (hnew : IsNewEigenform f)
    (ιp : MTT.Qbar →+* ℂ_[p]) (P : MTT.Periods k ι f.form) :
    Nonempty (IntegralPeriodScale f ιp P) := by sorry

end HorizontalPadicL
