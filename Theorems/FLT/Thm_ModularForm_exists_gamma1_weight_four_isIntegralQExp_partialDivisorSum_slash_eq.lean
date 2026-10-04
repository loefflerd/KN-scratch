import Mathlib
import Definitions.FLT.Def_ModularCurve_X1
import Definitions.FLT.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups ModularForm in
theorem ModularForm.exists_gamma1_weight_four_isIntegralQExp_partialDivisorSum_slash_eq
    (M : ℕ) [NeZero M] (hM : 3 ≤ M) :
    ∃ R : (ZMod M)ˣ → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) 4,
      (∀ c : (ZMod M)ˣ, ModularCurve.IsIntegralQExp (R c)
        (PowerSeries.mk fun n : ℕ => if n = 0 then 0 else
          ∑ d ∈ n.divisors,
            if ((n / d : ℕ) : ZMod M) = (c : ZMod M) ∨ ((n / d : ℕ) : ZMod M) = -(c : ZMod M)
            then (d : ℤ) ^ 3 else 0)) ∧
      (∀ (c : (ZMod M)ˣ) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M),
        ((⇑(R c) : UpperHalfPlane → ℂ) ∣[(4 : ℤ)] (γ : GL (Fin 2) ℝ)) =
          ⇑(R (c * (CohCarrier.gamma0Units M ⟨γ, hγ⟩)⁻¹))) := by sorry
