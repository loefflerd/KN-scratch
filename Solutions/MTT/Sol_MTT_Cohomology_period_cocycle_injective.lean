import Theorems.MTT.Thm_MTT_Cohomology_period_reflected_cusp_form
import Theorems.MTT.Thm_MTT_Cohomology_principal_period_equivariant_primitive
import Theorems.MTT.Thm_MTT_Cohomology_equivariant_primitive_pairings_zero
import Theorems.MTT.Thm_MTT_Cohomology_period_pairing_petersson_definite

noncomputable section
open scoped ComplexConjugate
open MTT.Cohomology

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (g h : CuspForm (MTT.GammaOne N) (k : ℤ)) (P : Binary ℂ)
    (hP : P ∈ MTT.Cohomology.Sym ℂ (k - 2))
    (hcob : ∀ γ : CongruenceSubgroup.Gamma1 N,
      cuspPrimitive g (cuspAct γ.val OnePoint.infty) +
        act !![-1, 0; 0, 1] (cuspPrimitive h
          (fractional !![-1, 0; 0, 1] (cuspAct γ.val OnePoint.infty))) =
      act γ.val.val P - P) :
    g = 0 ∧ h = 0 := by
  obtain ⟨v, hv, hvzero⟩ := period_reflected_cusp_form hN hk h
  obtain ⟨U, hU⟩ := principal_period_equivariant_primitive hN hk g h P hP hcob v hv
  have hp := equivariant_primitive_pairings_zero hN hk g v U hU
  have hgzero : g = 0 := (period_pairing_petersson_definite hN hk g).2.mp (hp g).1
  have hvzero' : v = 0 := (period_pairing_petersson_definite hN hk v).2.mp (hp v).2
  exact ⟨hgzero, hvzero.mp hvzero'⟩
