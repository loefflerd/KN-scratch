import Mathlib.NumberTheory.ModularForms.DedekindEta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem CuspForm.exists_gamma0_apply_eq_eta_mul_pow_twentyfour (N : ℕ) [NeZero N] :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) 12,
      ∀ τ : UpperHalfPlane, g τ = ModularForm.eta (N * (τ : ℂ)) ^ 24 := by sorry
