import Definitions.MTT.Def_MTT_PeriodPairing

noncomputable section
open scoped ComplexConjugate
open MTT.Cohomology

theorem MTT.Cohomology.equivariant_primitive_pairings_zero
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (g v : CuspForm (MTT.GammaOne N) (k : ℤ))
    (U : ℂ → Binary ℂ) (hU : IsMixedPeriodPrimitive g v U) :
    ∀ q : CuspForm (MTT.GammaOne N) (k : ℤ),
      periodPairing N (k - 2) g q = 0 ∧
      periodPairing N (k - 2) q v = 0 := by sorry
