import Definitions.FLT.Def_ModularCurve_X0
import Definitions.FLT.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.ModularPolynomialData.transposeToAdjoin_monic_of_qExpansion {N : ℕ} [NeZero N] (data : ModularPolynomialData N) (h0top : (evalAtJ (data.Φ.coeff 0)).coeff (-(dedekindPsi N : ℤ)) = 1) (h0le : ∀ m : ℕ, dedekindPsi N < m → (evalAtJ (data.Φ.coeff 0)).coeff (-(m : ℤ)) = 0) (hk : ∀ k, k ≠ 0 → ∀ m : ℕ, dedekindPsi N ≤ m → (evalAtJ (data.Φ.coeff k)).coeff (-(m : ℤ)) = 0) : ((swapBivar data.Φ).map evalAtJGen).Monic ∧ ((swapBivar data.Φ).map evalAtJGen).natDegree = dedekindPsi N := by sorry
