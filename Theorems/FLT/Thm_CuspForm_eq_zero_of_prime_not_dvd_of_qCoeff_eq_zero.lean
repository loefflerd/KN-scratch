import Definitions.FLT.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero
    {m p : ℕ} [NeZero m] (hp : p.Prime) (hpm : ¬ p ∣ m)
    (F : CuspForm (CongruenceSubgroup.Gamma0 m) 2)
    (hF : ∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff F n = 0) : F = 0 := by sorry
