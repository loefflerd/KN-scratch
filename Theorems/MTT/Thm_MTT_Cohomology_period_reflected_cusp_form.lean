import Definitions.MTT.Def_MTT_PeriodPairing

noncomputable section
open scoped ComplexConjugate
open MTT.Cohomology

theorem MTT.Cohomology.period_reflected_cusp_form
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (h : CuspForm (MTT.GammaOne N) (k : ℤ)) :
    ∃ v : CuspForm (MTT.GammaOne N) (k : ℤ),
      (∀ z : UpperHalfPlane, conj (v z) = h (periodReflect z)) ∧
      (v = 0 ↔ h = 0) := by sorry
