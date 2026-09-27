import Definitions.MTT.Def_MTT_PeriodPairing

set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open MTT.Cohomology

theorem MTT.Cohomology.period_pairing_petersson_definite
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (f : CuspForm (MTT.GammaOne N) (k : ℤ)) :
    periodPairing N (k - 2) f f =
      (2 * Complex.I) ^ (k - 2) * periodPetersson N k f f ∧
    (periodPairing N (k - 2) f f = 0 ↔ f = 0) := by sorry
