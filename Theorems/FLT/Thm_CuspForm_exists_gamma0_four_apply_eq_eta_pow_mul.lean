import Mathlib.NumberTheory.ModularForms.DedekindEta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
theorem CuspForm.exists_gamma0_four_apply_eq_eta_pow_mul (a b c : ℕ) (h0 : 0 < a + b + c)
    (h₁ : 24 ∣ a + 2 * b + 4 * c) (h₂ : 24 ∣ 4 * a + 2 * b + c) (hb : Even b) (h4 : 4 ∣ a + b + c) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 4) (((a + b + c) / 2 : ℕ) : ℤ),
      ∀ z : UpperHalfPlane, f z = ModularForm.eta (z : ℂ) ^ a * ModularForm.eta (2 * (z : ℂ)) ^ b *
        ModularForm.eta (4 * (z : ℂ)) ^ c := by sorry
