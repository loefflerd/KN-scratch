import Definitions.FLT.Def_CohCarrier_Level
import Definitions.FLT.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups ModularForm in
theorem ModularCurve.exists_intSeriesC_mul_ne_of_gamma0Units_not_mem
    (K : Type*) [Field K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0) (H : Subgroup (ZMod M)ˣ)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M)
    (hd : CohCarrier.gamma0Units M ⟨γ, hγ⟩ ∉ H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)) :
    ∃ (k : ℤ) (f g f₁ g₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
      (pf pg pf₁ pg₁ : PowerSeries ℤ) (c : ℂ), c ≠ 0 ∧
      ModularCurve.IsIntegralQExp f pf ∧ ModularCurve.IsIntegralQExp g pg ∧
      ModularCurve.IsIntegralQExp f₁ pf₁ ∧ ModularCurve.IsIntegralQExp g₁ pg₁ ∧
      (⇑f₁ : UpperHalfPlane → ℂ) = c • ((⇑f : UpperHalfPlane → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)) ∧
      (⇑g₁ : UpperHalfPlane → ℂ) = c • ((⇑g : UpperHalfPlane → ℂ) ∣[k] (γ : GL (Fin 2) ℝ)) ∧
      ModularCurve.intSeriesC K pg ≠ 0 ∧ ModularCurve.intSeriesC K pg₁ ≠ 0 ∧
      ModularCurve.intSeriesC K pf * ModularCurve.intSeriesC K pg₁ ≠
        ModularCurve.intSeriesC K pg * ModularCurve.intSeriesC K pf₁ := by sorry
