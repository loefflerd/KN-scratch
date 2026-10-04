import Mathlib.NumberTheory.DirichletCharacter.Basic

import Definitions.FLT.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CongruenceSubgroup
open scoped MatrixGroups
theorem ModularForm.exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd
    (L : ℕ) [NeZero L] (χ : DirichletCharacter ℂ L) (hχ : χ.IsPrimitive) (hodd : χ.Odd) :
    ∃ E : ModularForm (Gamma1 L) 1,
      (∀ γ : SL(2, ℤ), γ ∈ Gamma0 L → ∀ τ : UpperHalfPlane,
        E (γ • τ) =
          χ ((γ 1 1 : ℤ) : ZMod L) *
            ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ (1 : ℤ) * E τ)) ∧
      ModularFormClass.qCoeff E 0 =
        -(∑ a ∈ Finset.range L, (a : ℂ) * χ (a : ZMod L)) / (2 * L) ∧
      ∀ n : ℕ, 0 < n → ModularFormClass.qCoeff E n = ∑ d ∈ n.divisors, χ (d : ZMod L) := by sorry
