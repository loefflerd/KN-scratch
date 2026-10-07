module

public import Definitions.MTT.Def_MTT_Cohomology_Boundary

import Theorems.MTT.Thm_MTT_Cohomology_character_law_of_class
import Theorems.MTT.Thm_MTT_exists_cuspForm_heckePrime_pos
import Theorems.MTT.Thm_MTT_hasSum_heckePrime
import Theorems.MTT.Thm_MTT_coeff_eq_of_hecke_recurrence
import Theorems.MTT.Thm_MTT_period_vanishing

section privateSection

noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

namespace MTT.Cohomology

/-- `1` is a strict period of `Γ₁(N)` viewed inside `GL₂(ℝ)`. -/
theorem one_mem_strictPeriods_gammaOne (N : ℕ) :
    (1 : ℝ) ∈ (MTT.GammaOne N).strictPeriods := by
  rw [show MTT.GammaOne N = (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
    CongruenceSubgroup.strictPeriods_Gamma1]
  exact ⟨1, by simp⟩

/-- Any integration map is injective: this is `period_vanishing` read through `IntegralClass`. -/
theorem injective_of_integralClass {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ)
    (hI : ∀ f, IntegralClass f (I f)) : Function.Injective I := by
  intro f g hfg
  have h0 : I (f - g) = 0 := by rw [map_sub, hfg, sub_self]
  have hcls := hI (f - g)
  rw [h0] at hcls
  have hzero : f - g = 0 := MTT.period_vanishing hN hk (f - g) (fun j hj r => by
    have h := hcls j r hj
    rw [map_zero] at h
    have hch : (((k-2).choose j : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj).ne'
    exact (mul_eq_zero.mp h.symm).resolve_left hch)
  exact sub_eq_zero.mp hzero

end MTT.Cohomology

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ)
    (hI : ∀ f, IntegralClass f (I f)) (hT : HeckeEquivariant I)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) (g : CuspForm (MTT.GammaOne N) (k : ℤ))
    (hlaw : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      (I g).val (cuspAct γ.val x, cuspAct γ.val y) =
        ι (f.epsilon (γ.val 1 1 : ZMod N)) • act γ.val.val ((I g).val (x, y)))
    (hH : ∀ l : ℕ, l.Prime →
      primeHecke (ι (f.epsilon (l : ZMod N))) l (I g).val = ι (f.coeff l) • (I g).val) :
    ∃ c : ℂ, g = c • f.form := by
  -- q-expansions at the cusp ∞ of Γ₁(N), which has width one
  have h1 : (1 : ℝ) ∈ (MTT.GammaOne N).strictPeriods := one_mem_strictPeriods_gammaOne N
  have : Fact (IsCusp OnePoint.infty (MTT.GammaOne N)) :=
    ⟨(MTT.GammaOne N).isCusp_of_mem_strictPeriods one_pos h1⟩
  have hfa : ∀ σ : UpperHalfPlane,
      HasSum (fun n ↦ ι (f.coeff n) • Function.Periodic.qParam (1 : ℝ) (σ : ℂ) ^ n)
        (f.form σ) := by
    intro σ
    have := ModularForm.hasSum_qExpansion f.form one_pos h1 σ
    simpa [f.coeff_eq, smul_eq_mul] using this
  have hgb : ∀ σ : UpperHalfPlane,
      HasSum (fun n ↦ (UpperHalfPlane.qExpansion 1 g).coeff n •
        Function.Periodic.qParam (1 : ℝ) (σ : ℂ) ^ n) (g σ) := by
    intro σ
    have := ModularForm.hasSum_qExpansion g one_pos h1 σ
    simpa [smul_eq_mul] using this
  -- the nebentype law for `g` itself
  have hglaw := character_law_of_class hN hk I hI (fun d => ι (f.epsilon d)) g hlaw
  let e : DirichletCharacter ℂ N := f.epsilon.ringHomComp ι
  have he : ∀ d : ZMod N, e d = ι (f.epsilon d) := fun d => rfl
  have hinj := injective_of_integralClass hN hk I hI
  -- the Hecke eigen-equations for `g`, transported through `I`
  have hgeig : ∀ l : ℕ, l.Prime → ∀ z : UpperHalfPlane,
      MTT.heckePrime k (ι (f.epsilon l)) l g z = ι (f.coeff l) * g z := by
    intro l hl
    obtain ⟨gl, hgl, -⟩ := MTT.exists_cuspForm_heckePrime_pos hN (by omega) e g
      (fun γ z => by rw [he]; exact hglaw γ z) l hl
    have hIgl : (I gl).val = primeHecke (e l) l (I g).val := hT e l hl g gl hgl
    have hEq : I gl = I (ι (f.coeff l) • g) := by
      apply Subtype.ext
      rw [hIgl, he, hH l hl, map_smul]
      rfl
    have hgl' := hinj hEq
    intro z
    rw [← he, ← hgl, hgl']
    simp
  -- the coefficient recurrences, by comparing q-expansions
  have hrec_b : ∀ p : ℕ, p.Prime → ∀ m : ℕ,
      (UpperHalfPlane.qExpansion 1 g).coeff (p * m) +
        ι (f.epsilon p) * (p : ℂ) ^ (k - 1) *
          (if p ∣ m then (UpperHalfPlane.qExpansion 1 g).coeff (m / p) else 0) =
        ι (f.coeff p) * (UpperHalfPlane.qExpansion 1 g).coeff m := by
    intro p hp m
    have hs1 : ∀ τ : UpperHalfPlane, HasSum (fun n ↦
        ((UpperHalfPlane.qExpansion 1 g).coeff (p * n) + ι (f.epsilon p) * (p : ℂ) ^ (k - 1) *
          (if p ∣ n then (UpperHalfPlane.qExpansion 1 g).coeff (n / p) else 0)) •
          Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ n) ((ι (f.coeff p) • g) τ) := by
      intro τ
      have := MTT.hasSum_heckePrime k (ι (f.epsilon p)) hp (g : UpperHalfPlane → ℂ)
        (fun n ↦ (UpperHalfPlane.qExpansion 1 g).coeff n) τ hgb
      rw [hgeig p hp τ] at this
      simpa [smul_eq_mul] using this
    have hs2 : ∀ τ : UpperHalfPlane, HasSum (fun n ↦
        (ι (f.coeff p) * (UpperHalfPlane.qExpansion 1 g).coeff n) •
          Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ n) ((ι (f.coeff p) • g) τ) := by
      intro τ
      have := (hgb τ).const_smul (ι (f.coeff p))
      simpa [smul_eq_mul, mul_assoc] using this
    have u1 := ModularFormClass.qExpansion_coeff_unique one_pos h1 (f := ι (f.coeff p) • g) hs1 m
    have u2 := ModularFormClass.qExpansion_coeff_unique one_pos h1 (f := ι (f.coeff p) • g) hs2 m
    exact u1.trans u2.symm
  have hrec_a : ∀ p : ℕ, p.Prime → ∀ m : ℕ,
      ι (f.coeff (p * m)) + ι (f.epsilon p) * (p : ℂ) ^ (k - 1) *
          (if p ∣ m then ι (f.coeff (m / p)) else 0) =
        ι (f.coeff p) * ι (f.coeff m) := by
    intro p hp m
    have hs1 : ∀ τ : UpperHalfPlane, HasSum (fun n ↦
        (ι (f.coeff (p * n)) + ι (f.epsilon p) * (p : ℂ) ^ (k - 1) *
          (if p ∣ n then ι (f.coeff (n / p)) else 0)) •
          Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ n) ((ι (f.coeff p) • f.form) τ) := by
      intro τ
      have := MTT.hasSum_heckePrime k (ι (f.epsilon p)) hp (f.form : UpperHalfPlane → ℂ)
        (fun n ↦ ι (f.coeff n)) τ hfa
      rw [f.eigen p hp τ] at this
      simpa [smul_eq_mul] using this
    have hs2 : ∀ τ : UpperHalfPlane, HasSum (fun n ↦
        (ι (f.coeff p) * ι (f.coeff n)) •
          Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ n) ((ι (f.coeff p) • f.form) τ) := by
      intro τ
      have := (hfa τ).const_smul (ι (f.coeff p))
      simpa [smul_eq_mul, mul_assoc] using this
    have u1 := ModularFormClass.qExpansion_coeff_unique one_pos h1 (f := ι (f.coeff p) • f.form) hs1 m
    have u2 := ModularFormClass.qExpansion_coeff_unique one_pos h1 (f := ι (f.coeff p) • f.form) hs2 m
    exact u1.trans u2.symm
  -- constant terms vanish
  have hb0 : (UpperHalfPlane.qExpansion 1 g).coeff 0 = 0 :=
    CuspFormClass.qExpansion_coeff_zero g one_pos h1
  have ha0 : ι (f.coeff 0) = 0 := by
    rw [← f.coeff_eq 0]
    exact CuspFormClass.qExpansion_coeff_zero f.form one_pos h1
  -- the recurrence determines the coefficients from the first one
  have hP2 := MTT.coeff_eq_of_hecke_recurrence k (fun p => ι (f.epsilon p)) (fun p => ι (f.coeff p))
    (fun n => (UpperHalfPlane.qExpansion 1 g).coeff n) (fun n => ι (f.coeff n)) hrec_b hrec_a
    (by simp [f.normalized])
  refine ⟨(UpperHalfPlane.qExpansion 1 g).coeff 1, ?_⟩
  ext τ
  have h2 : HasSum (fun n ↦ (UpperHalfPlane.qExpansion 1 g).coeff n •
      Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ n)
      ((UpperHalfPlane.qExpansion 1 g).coeff 1 • f.form τ) := by
    have := (hfa τ).const_smul ((UpperHalfPlane.qExpansion 1 g).coeff 1)
    convert this using 1
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hb0, ha0]
    · rw [hP2 n hn, smul_smul]
  exact (hgb τ).unique h2
end

end privateSection

public section publicSection

noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.image_packet_unique
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ)
    (hI : ∀ f, IntegralClass f (I f)) (hT : HeckeEquivariant I)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) (g : CuspForm (MTT.GammaOne N) (k : ℤ))
    (hlaw : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      (I g).val (cuspAct γ.val x, cuspAct γ.val y) =
        ι (f.epsilon (γ.val 1 1 : ZMod N)) • act γ.val.val ((I g).val (x, y)))
    (hH : ∀ l : ℕ, l.Prime →
      primeHecke (ι (f.epsilon (l : ZMod N))) l (I g).val = ι (f.coeff l) • (I g).val) :
    ∃ c : ℂ, g = c • f.form := _root_.solution hN hk I hI hT ι f g hlaw hH
end

end publicSection
