import Definitions.MTT.Def_MTT_Arithmetic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

set_option autoImplicit false
noncomputable section

theorem MTT.Eigenform.heckeEigenvalue_isIntegral
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (l : ℕ) (hl : l.Prime) :
    IsIntegral ℤ (f.coeff l) := by
  sorry
