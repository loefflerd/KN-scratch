import Definitions.MTT.Def_MTT_Cohomology_Boundary
import Mathlib.NumberTheory.LSeries.PrimesInAP
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MTT.Cohomology

theorem MTT.cusp_log_weighted_square_summable
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (f : CuspForm (MTT.GammaOne N) (k : ℤ)) :
    Summable (fun m : ℕ =>
      ‖(UpperHalfPlane.qExpansion 1 f).coeff m‖^2 * Real.log m /
        (m : ℝ)^(k+1)) := by sorry
