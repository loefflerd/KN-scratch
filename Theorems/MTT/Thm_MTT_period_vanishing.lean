import Definitions.MTT.Def_MTT_Arithmetic
noncomputable section
open scoped BigOperators

theorem MTT.period_vanishing
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (f : CuspForm (MTT.GammaOne N) (k : ℤ))
    (h : ∀ j : ℕ, j ≤ k - 2 → ∀ r : ℚ,
      MTT.modularIntegral f (Polynomial.X ^ j) r = 0) :
    f = 0 := by sorry
