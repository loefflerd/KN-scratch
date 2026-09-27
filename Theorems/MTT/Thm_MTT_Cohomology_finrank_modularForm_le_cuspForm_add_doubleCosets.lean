import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
open scoped MatrixGroups

theorem MTT.Cohomology.finrank_modularForm_le_cuspForm_add_doubleCosets
    (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] (k : ℤ) :
    Module.finrank ℂ (ModularForm H k) ≤ Module.finrank ℂ (CuspForm H k) +
      Nat.card (DoubleCoset.Quotient (H : Set SL(2, ℤ))
        ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) :
          Set SL(2, ℤ))) := by sorry
