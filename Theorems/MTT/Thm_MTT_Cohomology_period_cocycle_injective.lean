import Definitions.MTT.Def_MTT_Cohomology_Integration

noncomputable section
open MTT.Cohomology
theorem MTT.Cohomology.period_cocycle_injective
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (g h : CuspForm (MTT.GammaOne N) (k : ℤ)) (P : Binary ℂ)
    (hP : P ∈ Sym ℂ (k - 2))
    (hcob : ∀ γ : CongruenceSubgroup.Gamma1 N,
      cuspPrimitive g (cuspAct γ.val OnePoint.infty) +
        act !![-1, 0; 0, 1] (cuspPrimitive h
          (fractional !![-1, 0; 0, 1] (cuspAct γ.val OnePoint.infty))) =
      act γ.val.val P - P) :
    g = 0 ∧ h = 0 := by sorry
