import Theorems.MTT.Thm_MTT_sum_integral_wirtinger_smul_fd_eq_zero
import Theorems.MTT.Thm_MTT_Cohomology_gammaOne_has_finset_complement
import Theorems.MTT.Thm_MTT_Cohomology_mixed_period_test_functions_wirtinger_data_of_pos_level
import Theorems.MTT.Thm_MTT_Cohomology_period_pairings_eq_wirtinger_sums_of_weight_ge_two

noncomputable section
open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Modular ComplexConjugate
open MTT.Cohomology

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (g v : CuspForm (MTT.GammaOne N) (k : ℤ))
    (U : ℂ → Binary ℂ) (hU : IsMixedPeriodPrimitive g v U) :
    ∀ q : CuspForm (MTT.GammaOne N) (k : ℤ),
      periodPairing N (k - 2) g q = 0 ∧
      periodPairing N (k - 2) q v = 0 := by
  intro q
  obtain ⟨R, hR⟩ := gammaOne_has_finset_complement hN
  obtain ⟨A₁, A₂, hA₁, hinv₁, hdecay₁, hint₁, hderiv₁,
      hA₂, hinv₂, hdecay₂, hint₂, hderiv₂⟩ :=
    mixed_period_test_functions_wirtinger_data_of_pos_level hN hk g v q U hU R
  have hz₁ := MTT.sum_integral_wirtinger_smul_fd_eq_zero
    (Γ := CongruenceSubgroup.Gamma1 N) hR hA₁ hinv₁ hdecay₁ hint₁
  have hz₂ := MTT.sum_integral_wirtinger_smul_fd_eq_zero
    (Γ := CongruenceSubgroup.Gamma1 N) hR hA₂ hinv₂ hdecay₂ hint₂
  obtain ⟨hp₁, hp₂⟩ :=
    period_pairings_eq_wirtinger_sums_of_weight_ge_two
      hk g v q R hR hint₁ hint₂ hderiv₁ hderiv₂
  constructor
  · rw [hp₁]
    exact hz₁
  · rw [hp₂, hz₂]
    simp
