module

public import Definitions.KN.Def_KN_HorizontalPadicLAux
public import Definitions.FLT.Def_FLTPrelim_Modularity
public import Theorems.MTT.Thm_MTT_hasSum_heckePrime
public import Theorems.KN.Thm_HorizontalPadicL_ellipticCurve_attachedForm_isNormalizedEigenform

@[expose] public section publicSection

set_option autoImplicit false
noncomputable section

open scoped ModularForm

namespace HorizontalPadicL

def gammaZeroToGammaOne {N : ℕ} (hN : 0 < N)
    (f : CuspFormAtLevel N hN) : CuspForm (MTT.GammaOne N) 2 where
  toFun := f
  slash_action_eq' := fun A hA =>
    f.slash_action_eq' A (Subgroup.map_mono (CongruenceSubgroup.Gamma1_in_Gamma0 N) hA)
  holo' := f.holo'
  zero_at_cusps' hc := by
    let : NeZero N := ⟨Nat.ne_of_gt hN⟩
    apply f.zero_at_cusps'
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
    rwa [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc

@[simp] theorem gammaZeroToGammaOne_apply {N : ℕ} (hN : 0 < N)
    (f : CuspFormAtLevel N hN) (z : UpperHalfPlane) :
    gammaZeroToGammaOne hN f z = f z := rfl

lemma normalizedEigenform_hecke_recurrence {N : ℕ} {hN : 0 < N}
    {f : CuspFormAtLevel N hN} (hf : f.IsNormalizedEigenform)
    (p n : ℕ) (hp : p.Prime) :
    ModularFormClass.qCoeff f (p * n) +
        (if p ∣ N then 0 else (p : ℂ)) *
          (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
      ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n := by
  by_cases hn0 : n = 0
  · subst n
    have ha0 : ModularFormClass.qCoeff f 0 = 0 := by
      simpa [ModularFormClass.qCoeff, CongruenceSubgroup.strictPeriods_Gamma0] using
        (CuspFormClass.qExpansion_coeff_zero f one_pos
          (show (1 : ℝ) ∈
            (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods by simp))
    simp [ha0]
  · obtain ⟨r, m, hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.ne_one
    have hc : (p ^ r).Coprime m := (hp.coprime_iff_not_dvd.mpr hpm).pow_left r
    have hc1 : (p ^ (r + 1)).Coprime m := (hp.coprime_iff_not_dvd.mpr hpm).pow_left (r + 1)
    have hc2 : (p ^ (r + 2)).Coprime m := (hp.coprime_iff_not_dvd.mpr hpm).pow_left (r + 2)
    rw [show p * (p ^ r * m) = p ^ (r + 1) * m by ring,
      hf.qCoeff_mul_of_coprime _ _ hc1,
      hf.qCoeff_mul_of_coprime _ _ hc]
    cases r with
    | zero =>
        simp [hf.qCoeff_one, hpm]
    | succ r =>
        have hdiv : p ∣ p ^ (r + 1) * m := ⟨p ^ r * m, by ring⟩
        rw [ite_eq_left hdiv]
        have hquot : (p ^ (r + 1) * m) / p = p ^ r * m := by
          simp [pow_succ, hp.ne_zero, mul_assoc, mul_left_comm]
        rw [hquot]
        by_cases hpN : p ∣ N
        · rw [ite_eq_left hpN]
          simp only [zero_mul, add_zero]
          rw [show r + 1 + 1 = r + 2 by omega]
          rw [hf.qCoeff_prime_pow_of_dvd p r hp hpN]
          ring
        · rw [ite_eq_right hpN]
          rw [hf.qCoeff_mul_of_coprime _ _ ((hp.coprime_iff_not_dvd.mpr hpm).pow_left r)]
          rw [show r + 1 + 1 = r + 2 by omega]
          rw [hf.qCoeff_prime_pow_of_not_dvd p r hp hpN]
          ring

def attachedEigenformCandidate (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hmod : IsModular E) (hnormalized :
      CuspForm.IsNormalizedEigenform (modularFormAtConductor E hmod).form)
    (iota : MTT.Qbar →+* ℂ) :
    MTT.Eigenform (modularConductor E hmod) 2 iota where
  form := gammaZeroToGammaOne (modularConductor_pos E hmod)
    (modularFormAtConductor E hmod).form
  epsilon := 1
  coeff n := (E.LFunction n : MTT.Qbar)
  coeff_eq n := by
    change (UpperHalfPlane.qExpansion 1 (modularFormAtConductor E hmod).form).coeff n = _
    rw [← (modularFormAtConductor E hmod).coeff_eq n]
    simp
  normalized := by
    have hc : ((E.LFunction 1 : ℤ) : ℂ) = 1 := by
      simpa [ModularFormClass.qCoeff, ← (modularFormAtConductor E hmod).coeff_eq 1]
        using hnormalized.qCoeff_one
    exact_mod_cast hc
  character_law gamma z := by
    have hdet : ((gamma.val 0 0 : ℤ) : ZMod (modularConductor E hmod)) *
        (gamma.val 1 1 : ZMod (modularConductor E hmod)) = 1 := by
      have hd := congrArg (fun x : ℤ => (x : ZMod (modularConductor E hmod)))
        gamma.val.property
      rw [Matrix.det_fin_two] at hd
      simpa [CongruenceSubgroup.Gamma0_mem.mp gamma.property] using hd
    have hunit : IsUnit (gamma.val 1 1 : ZMod (modularConductor E hmod)) := by
      apply isUnit_iff_exists_inv.mpr
      exact ⟨(gamma.val 0 0 : ZMod (modularConductor E hmod)), by
        simpa [mul_comm] using hdet⟩
    have hone : (1 : DirichletCharacter MTT.Qbar (modularConductor E hmod))
        (gamma.val 1 1 : ZMod (modularConductor E hmod)) = 1 := by
      exact MulChar.one_apply hunit
    have h := (ModularForm.slash_action_eq'_iff 2
      (modularFormAtConductor E hmod).form gamma.val z).mp
        (congrFun ((modularFormAtConductor E hmod).form.slash_action_eq'
          (Matrix.SpecialLinearGroup.mapGL ℝ gamma.val) ⟨gamma.val, gamma.property, rfl⟩) z)
    simp only [hone, map_one, one_mul]
    convert h using 1 <;> rfl
  eigen p hp z := by
    let P := modularFormAtConductor E hmod
    let a : ℕ → ℂ := fun n => ModularFormClass.qCoeff P.form n
    have hper : Function.Periodic (P.form ∘ UpperHalfPlane.ofComplex) 1 := by
      simpa using SlashInvariantFormClass.periodic_comp_ofComplex P.form
        (show (1 : ℝ) ∈
          (CongruenceSubgroup.Gamma0 (modularConductor E hmod) :
            Subgroup (GL (Fin 2) ℝ)).strictPeriods by
          simp [CongruenceSubgroup.strictPeriods_Gamma0])
    have hsum : ∀ w : UpperHalfPlane,
        HasSum (fun n => a n • Function.Periodic.qParam (1 : ℝ) (w : ℂ) ^ n)
          (P.form w) := by
      intro w
      let : NeZero (modularConductor E hmod) :=
        ⟨Nat.ne_of_gt (modularConductor_pos E hmod)⟩
      exact UpperHalfPlane.hasSum_qExpansion one_pos hper P.form.holo'
        (CuspFormClass.zero_at_infty P.form).isBoundedAtImInfty w
    have heps : iota ((1 : DirichletCharacter MTT.Qbar (modularConductor E hmod)) p) =
        if p ∣ modularConductor E hmod then 0 else 1 := by
      by_cases hpN : p ∣ modularConductor E hmod
      · rw [ite_eq_left hpN]
        have hnonunit : ¬ IsUnit (p : ZMod (modularConductor E hmod)) := by
          exact fun hunit => ((ZMod.isUnit_prime_iff_not_dvd hp).mp hunit) hpN
        change iota (MulChar.trivial (ZMod (modularConductor E hmod)) MTT.Qbar p) = 0
        simp [MulChar.trivial, hnonunit]
      · rw [ite_eq_right hpN]
        have hunit : IsUnit (p : ZMod (modularConductor E hmod)) := by
          exact (ZMod.isUnit_prime_iff_not_dvd hp).mpr hpN
        simp [MulChar.one_apply hunit]
    have hhecke := MTT.hasSum_heckePrime 2
      (iota ((1 : DirichletCharacter MTT.Qbar (modularConductor E hmod)) p)) hp
      (P.form : UpperHalfPlane → ℂ) a z hsum
    have hscalar := (hsum z).const_smul (a p)
    rw [heps] at hhecke
    have hterms : ∀ n : ℕ,
        (a (p * n) + (if p ∣ modularConductor E hmod then 0 else 1) *
          (p : ℂ) ^ (2 - 1) * (if p ∣ n then a (n / p) else 0)) =
          a p * a n := by
      intro n
      simpa [mul_assoc] using
        (normalizedEigenform_hecke_recurrence hnormalized p n hp)
    rw [show MTT.heckePrime 2
      (iota ((1 : DirichletCharacter MTT.Qbar (modularConductor E hmod)) p)) p
      (gammaZeroToGammaOne (modularConductor_pos E hmod) P.form) z =
        MTT.heckePrime 2
          (iota ((1 : DirichletCharacter MTT.Qbar (modularConductor E hmod)) p)) p
          P.form z by rfl]
    change MTT.heckePrime 2
      (iota ((1 : DirichletCharacter MTT.Qbar (modularConductor E hmod)) p)) p
      P.form z = iota (E.LFunction p : MTT.Qbar) * P.form z
    rw [heps]
    have hcoeff : iota (E.LFunction p : MTT.Qbar) = a p := by
      simpa [a, ModularFormClass.qCoeff] using P.coeff_eq p
    rw [hcoeff]
    change MTT.heckePrime 2
      (if p ∣ modularConductor E hmod then 0 else 1) p
      P.form z = a p * P.form z
    apply HasSum.unique hhecke
    simpa only [hterms, smul_eq_mul, ← mul_assoc] using hscalar

/-- The weight-two eigenform associated with E at its least modular level. -/
noncomputable def attachedEigenform (iota : MTT.Qbar →+* ℂ)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (hmod : IsModular E) :
    MTT.Eigenform (modularConductor E hmod) 2 iota :=
  attachedEigenformCandidate E hmod
    (ellipticCurve_attachedForm_isNormalizedEigenform E hmod) iota

@[simp] theorem attachedEigenform_coeff (iota : MTT.Qbar →+* ℂ)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (hmod : IsModular E) (n : ℕ) :
    (attachedEigenform iota E hmod).coeff n = (E.LFunction n : MTT.Qbar) := rfl

@[simp] theorem attachedEigenform_epsilon (iota : MTT.Qbar →+* ℂ)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (hmod : IsModular E) :
    (attachedEigenform iota E hmod).epsilon = 1 := rfl

end HorizontalPadicL
end

end publicSection
