import Definitions.MTT.Def_MTT_Cohomology
import Mathlib.RingTheory.Flat.Basic
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.base_change
    {N n : ℕ} (hN : 0 < N) (R : Type*) [CommRing R] [Module.Flat ℤ R] :
    BaseChange N n R := by sorry
