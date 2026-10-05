module

public import Definitions.MTT.Def_MTT_Arithmetic

import Theorems.MTT.Thm_MTT_hasSum_heckePrime

section privateSection

noncomputable section

set_option linter.unusedVariables false in
theorem solution
    {N k : ℕ} (hN : 0 < N)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (q : ℕ) (hq : q.Prime) (m : ℕ) :
    f.coeff (q * m) + f.epsilon q * (q : MTT.Qbar) ^ (k - 1) *
        (if q ∣ m then f.coeff (m / q) else 0) =
      f.coeff q * f.coeff m := by
  have hperiod : (1 : ℝ) ∈ (MTT.GammaOne N).strictPeriods := by
    rw [show MTT.GammaOne N =
      (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
      CongruenceSubgroup.strictPeriods_Gamma1]
    exact ⟨1, by simp⟩
  have : Fact (IsCusp OnePoint.infty (MTT.GammaOne N)) :=
    ⟨(MTT.GammaOne N).isCusp_of_mem_strictPeriods one_pos hperiod⟩
  have hseries : ∀ z : UpperHalfPlane,
      HasSum (fun n ↦ ι (f.coeff n) •
        Function.Periodic.qParam (1 : ℝ) (z : ℂ) ^ n) (f.form z) := by
    intro z
    simpa [f.coeff_eq, smul_eq_mul] using
      (ModularForm.hasSum_qExpansion f.form one_pos hperiod z)
  have hrecC :
      ι (f.coeff (q * m)) + ι (f.epsilon q) * (q : ℂ) ^ (k - 1) *
          (if q ∣ m then ι (f.coeff (m / q)) else 0) =
        ι (f.coeff q) * ι (f.coeff m) := by
    have hs₁ : ∀ z : UpperHalfPlane, HasSum (fun r ↦
        (ι (f.coeff (q * r)) + ι (f.epsilon q) * (q : ℂ) ^ (k - 1) *
          (if q ∣ r then ι (f.coeff (r / q)) else 0)) •
          Function.Periodic.qParam (1 : ℝ) (z : ℂ) ^ r)
        ((ι (f.coeff q) • f.form) z) := by
      intro z
      have hs := MTT.hasSum_heckePrime k (ι (f.epsilon q)) hq
        (f.form : UpperHalfPlane → ℂ) (fun r ↦ ι (f.coeff r)) z hseries
      rw [f.eigen q hq z] at hs
      simpa [smul_eq_mul] using hs
    have hs₂ : ∀ z : UpperHalfPlane, HasSum (fun r ↦
        (ι (f.coeff q) * ι (f.coeff r)) •
          Function.Periodic.qParam (1 : ℝ) (z : ℂ) ^ r)
        ((ι (f.coeff q) • f.form) z) := by
      intro z
      simpa [smul_eq_mul, mul_assoc] using
        (hseries z).const_smul (ι (f.coeff q))
    have hu₁ := ModularFormClass.qExpansion_coeff_unique one_pos hperiod
      (f := ι (f.coeff q) • f.form) hs₁ m
    have hu₂ := ModularFormClass.qExpansion_coeff_unique one_pos hperiod
      (f := ι (f.coeff q) • f.form) hs₂ m
    exact hu₁.trans hu₂.symm
  apply ι.injective
  by_cases hdiv : q ∣ m
  · simpa [hdiv] using hrecC
  · simpa [hdiv] using hrecC
end

end privateSection

public section publicSection

noncomputable section

/-- The Fourier coefficients of an MTT eigenform satisfy the usual prime
Hecke recurrence. -/
theorem MTT.Eigenform.hecke_recurrence
    {N k : ℕ} (hN : 0 < N)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (q : ℕ) (hq : q.Prime) (m : ℕ) :
    f.coeff (q * m) + f.epsilon q * (q : MTT.Qbar) ^ (k - 1) *
        (if q ∣ m then f.coeff (m / q) else 0) =
      f.coeff q * f.coeff m := _root_.solution hN ι f q hq m
end

end publicSection
