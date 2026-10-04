import Definitions.MTT.Def_MTT_PeriodPairing

noncomputable section
open scoped ComplexConjugate
open MTT.Cohomology

theorem MTT.Cohomology.principal_period_equivariant_primitive
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (g h : CuspForm (MTT.GammaOne N) (k : ℤ)) (P : Binary ℂ)
    (hP : P ∈ Sym ℂ (k - 2))
    (hcob : ∀ γ : CongruenceSubgroup.Gamma1 N,
      cuspPrimitive g (cuspAct γ.val OnePoint.infty) +
        act !![-1, 0; 0, 1] (cuspPrimitive h
          (fractional !![-1, 0; 0, 1] (cuspAct γ.val OnePoint.infty))) =
      act γ.val.val P - P)
    (v : CuspForm (MTT.GammaOne N) (k : ℤ))
    (hv : ∀ z : UpperHalfPlane, conj (v z) = h (periodReflect z)) :
    ∃ U : ℂ → Binary ℂ, IsMixedPeriodPrimitive g v U := by sorry
