import Definitions.MTT.Def_MTT_Cohomology_Integration

noncomputable section
open MTT.Cohomology
theorem MTT.Cohomology.parabolic_period_cocycle_surjective
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (c : CongruenceSubgroup.Gamma1 N → Binary ℂ)
    (hsym : ∀ γ, c γ ∈ Sym ℂ (k - 2))
    (hcoc : ∀ γ δ, c (γ * δ) = c γ + act γ.val.val (c δ))
    (hpar : ∀ (x : Cusp) (γ : CongruenceSubgroup.Gamma1 N), cuspAct γ.val x = x →
      ∃ Q : Binary ℂ, Q ∈ Sym ℂ (k - 2) ∧ c γ = act γ.val.val Q - Q) :
    ∃ (g h : CuspForm (MTT.GammaOne N) (k : ℤ)) (P : Binary ℂ),
      P ∈ Sym ℂ (k - 2) ∧ ∀ γ : CongruenceSubgroup.Gamma1 N,
        c γ = cuspPrimitive g (cuspAct γ.val OnePoint.infty) +
          act !![-1, 0; 0, 1] (cuspPrimitive h
            (fractional !![-1, 0; 0, 1] (cuspAct γ.val OnePoint.infty))) +
          (act γ.val.val P - P) := by sorry
