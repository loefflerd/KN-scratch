import Definitions.MTT.Def_MTT_Arithmetic

set_option autoImplicit false
noncomputable section

/-- The Fourier coefficients of an MTT eigenform satisfy the usual prime
Hecke recurrence. -/
theorem MTT.Eigenform.hecke_recurrence
    {N k : ℕ} (hN : 0 < N)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (q : ℕ) (hq : q.Prime) (m : ℕ) :
    f.coeff (q * m) + f.epsilon q * (q : MTT.Qbar) ^ (k - 1) *
        (if q ∣ m then f.coeff (m / q) else 0) =
      f.coeff q * f.coeff m := by
  sorry
