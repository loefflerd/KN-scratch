import Definitions.MTT.Def_MTT_Arithmetic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

noncomputable section

theorem MTT.Eigenform.coeff_isIntegral
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) (n : ℕ) :
    IsIntegral ℤ (f.coeff n) := by
  sorry
