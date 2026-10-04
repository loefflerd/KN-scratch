import Theorems.KN.Thm_MTT_Eigenform_heckeEigenvalue_isIntegral
import Theorems.MTT.Thm_MTT_hasSum_heckePrime
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.NumberTheory.MulChar.Lemmas

noncomputable section

open scoped Polynomial

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) (n : ℕ) :
    IsIntegral ℤ (f.coeff n) := by
  have hperiod : (1 : ℝ) ∈ (MTT.GammaOne N).strictPeriods := by
    rw [show MTT.GammaOne N =
      (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
      CongruenceSubgroup.strictPeriods_Gamma1]
    exact ⟨1, by simp⟩
  have : Fact (IsCusp OnePoint.infty (MTT.GammaOne N)) :=
    ⟨(MTT.GammaOne N).isCusp_of_mem_strictPeriods one_pos hperiod⟩
  have hseries : ∀ z : UpperHalfPlane,
      HasSum (fun m ↦ ι (f.coeff m) •
        Function.Periodic.qParam (1 : ℝ) (z : ℂ) ^ m) (f.form z) := by
    intro z
    simpa [f.coeff_eq, smul_eq_mul] using
      (ModularForm.hasSum_qExpansion f.form one_pos hperiod z)
  have hrecC : ∀ q : ℕ, q.Prime → ∀ m : ℕ,
      ι (f.coeff (q * m)) + ι (f.epsilon q) * (q : ℂ) ^ (k - 1) *
          (if q ∣ m then ι (f.coeff (m / q)) else 0) =
        ι (f.coeff q) * ι (f.coeff m) := by
    intro q hq m
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
  have hrec : ∀ q : ℕ, q.Prime → ∀ m : ℕ,
      f.coeff (q * m) + f.epsilon q * (q : MTT.Qbar) ^ (k - 1) *
          (if q ∣ m then f.coeff (m / q) else 0) =
        f.coeff q * f.coeff m := by
    intro q hq m
    apply ι.injective
    by_cases hdiv : q ∣ m
    · simpa [hdiv] using hrecC q hq m
    · simpa [hdiv] using hrecC q hq m
  have hepsilon : ∀ a : ℕ, IsIntegral ℤ (f.epsilon a) := by
    intro a
    by_cases ha : f.epsilon a = 0
    · simpa [ha] using (isIntegral_zero : IsIntegral ℤ (0 : MTT.Qbar))
    · have hu : IsUnit (a : ZMod N) := MulChar.apply_ne_zero_iff.mp ha
      let := Fintype.ofFinite (ZMod N)ˣ
      let d := Fintype.card (ZMod N)ˣ
      have hd : 0 < d := Fintype.card_pos
      have hroot := f.epsilon.apply_mem_rootsOfUnity hu.unit
      have hpow : (f.epsilon a) ^ d = 1 := by
        simpa [IsUnit.unit_spec hu] using (mem_rootsOfUnity' d _).mp hroot
      refine ⟨Polynomial.X ^ d - 1,
        Polynomial.monic_X_pow_sub_C 1 (Nat.ne_of_gt hd), ?_⟩
      simp [hpow]
  have hzero : f.coeff 0 = 0 := by
    apply ι.injective
    rw [← f.coeff_eq 0]
    simpa using CuspFormClass.qExpansion_coeff_zero f.form one_pos hperiod
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _
      · simpa [hzero] using (isIntegral_zero : IsIntegral ℤ (0 : MTT.Qbar))
      · rename_i n
        by_cases hn : n + 1 = 1
        · simpa [hn, f.normalized] using (isIntegral_one : IsIntegral ℤ (1 : MTT.Qbar))
        · obtain ⟨q, hq, hqdiv⟩ := Nat.exists_prime_and_dvd hn
          let m := (n + 1) / q
          have hnpos : 0 < n + 1 := Nat.succ_pos n
          have hqgt : 1 < q := hq.one_lt
          have hm_lt : m < n + 1 := Nat.div_lt_self hnpos hqgt
          have hqm : q * m = n + 1 := Nat.mul_div_cancel' hqdiv
          have hmdiv_lt : m / q < n + 1 := lt_of_le_of_lt (Nat.div_le_self m q) hm_lt
          have hiq := MTT.Eigenform.heckeEigenvalue_isIntegral hN hk ι f q hq
          have him := ih m hm_lt
          have hicorr : IsIntegral ℤ
              (f.epsilon q * (q : MTT.Qbar) ^ (k - 1) *
                (if q ∣ m then f.coeff (m / q) else 0)) := by
            refine (hepsilon q).mul ((isIntegral_natCast q).pow (k - 1)) |>.mul ?_
            split
            · exact ih (m / q) hmdiv_lt
            · exact isIntegral_zero
          have heq := hrec q hq m
          rw [hqm] at heq
          have hint := (hiq.mul him).sub hicorr
          rw [← heq] at hint
          simpa using hint
