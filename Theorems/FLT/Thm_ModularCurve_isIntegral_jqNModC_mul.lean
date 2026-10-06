module

public import Definitions.FLT.Def_ModularCurve_X0
public import Definitions.FLT.Def_ModularCurve_JqCoeff

import Theorems.FLT.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isIntegral_jqNModC_mul

open ModularCurve IntermediateField Polynomial

private theorem isIntegral_of_eval₂_eq_zero {L : Type*} [Field L] (F : IntermediateField L (LaurentSeries L))
    {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic) {a b : LaurentSeries L} (ha : a ∈ F)
    (h : Φ.eval₂ (aeval (R := ℤ) a).toRingHom b = 0) : IsIntegral F b := by
  set ev : Polynomial ℤ →+* F := (aeval (R := ℤ) (⟨a, ha⟩ : F)).toRingHom with hev
  have hcomp : (algebraMap F (LaurentSeries L)).comp ev = (aeval (R := ℤ) a).toRingHom := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp [hev]
  refine ⟨Φ.map ev, hΦ.map ev, ?_⟩
  rw [Polynomial.eval₂_map, hcomp]
  exact h

theorem solution {K : Type*} [Field K] (F : IntermediateField K (LaurentSeries K)) {ℓ : ℕ} [NeZero ℓ] (data : ModularCurve.ModularPolynomialData ℓ) (d : ℕ) [NeZero d] (hd : ModularCurve.jqNModC K d ∈ F) : IsIntegral F (ModularCurve.jqNModC K (d * ℓ)) :=
  isIntegral_of_eval₂_eq_zero F data.monic hd (data.eval_jqNModC_mul_eq_zero K d)

end S_ModularCurve_isIntegral_jqNModC_mul
end P2MW
export P2MW.S_ModularCurve_isIntegral_jqNModC_mul (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.isIntegral_jqNModC_mul {K : Type*} [Field K] (F : IntermediateField K (LaurentSeries K)) {ℓ : ℕ} [NeZero ℓ] (data : ModularCurve.ModularPolynomialData ℓ) (d : ℕ) [NeZero d] (hd : ModularCurve.jqNModC K d ∈ F) : IsIntegral F (ModularCurve.jqNModC K (d * ℓ)) := _root_.P2MW.S_ModularCurve_isIntegral_jqNModC_mul.solution F data d hd

end publicSection
