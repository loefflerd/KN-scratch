import Definitions.MTT.Def_MTT_Arithmetic
set_option autoImplicit false
noncomputable section
open scoped BigOperators

theorem MTT.hasSum_heckePrime (k : ℕ) (e : ℂ) {p : ℕ} (hp : Nat.Prime p)
    (f : UpperHalfPlane → ℂ) (a : ℕ → ℂ) (τ : UpperHalfPlane)
    (hf : ∀ σ : UpperHalfPlane,
      HasSum (fun n ↦ a n • Function.Periodic.qParam (1 : ℝ) (σ : ℂ) ^ n) (f σ)) :
    HasSum (fun n ↦ (a (p * n) + e * (p : ℂ) ^ (k - 1) * (if p ∣ n then a (n / p) else 0)) •
        Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ n)
      (MTT.heckePrime k e p f τ) := by sorry
