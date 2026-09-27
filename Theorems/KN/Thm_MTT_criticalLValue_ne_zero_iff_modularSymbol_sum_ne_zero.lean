import Theorems.MTT.Thm_MTT_birch_mellin_formula

set_option autoImplicit false
noncomputable section
open scoped BigOperators

open MTT in
/-- For a primitive Dirichlet character, the scalar in the Birch--Mellin
formula is nonzero.  Thus the critical L-value vanishes exactly when its
character-weighted modular-symbol sum vanishes. -/
theorem MTT.criticalLValue_ne_zero_iff_modularSymbol_sum_ne_zero
    {N k m : ℕ} [NeZero m] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (f : Eigenform N k ι)
    (χ : DirichletCharacter Qbar m) (hχ : χ.IsPrimitive)
    (j : ℕ) (hj : j ≤ k - 2) :
    criticalLValue ι f.form m χ j ≠ 0 ↔
      (∑ a : ZMod m, ι (χ a) * modularSymbol f.form j a.val m) ≠ 0 := by
  sorry
