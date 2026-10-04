import Definitions.MTT.Def_MTT_Cohomology
import Mathlib.RingTheory.Flat.Basic
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.integral_finite_generation
    {N n : ℕ} (hN : 0 < N) : Module.Finite ℤ (Hc N n ℤ) := by sorry
