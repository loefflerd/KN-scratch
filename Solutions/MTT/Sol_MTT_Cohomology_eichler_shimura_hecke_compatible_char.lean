import Theorems.MTT.Thm_MTT_Cohomology_eichler_shimura_direct
import Theorems.MTT.Thm_MTT_Cohomology_primeHecke_boundary_datum
import Theorems.MTT.Thm_MTT_Cohomology_character_law_of_class
import Theorems.MTT.Thm_MTT_exists_cuspForm_heckePrime_pos
import Theorems.MTT.Thm_MTT_Cohomology_reflection_class
import Theorems.MTT.Thm_MTT_Cohomology_reflection_involutive
import Definitions.MTT.Def_MTT_Cohomology_Boundary
import Mathlib.RingTheory.Flat.Basic
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

namespace MTT.Cohomology

lemma reflection_add {R : Type*} [CommRing R] (φ ψ : (Cusp × Cusp) → Binary R) :
    reflection (φ + ψ) = reflection φ + reflection ψ := by
  funext D; simp [reflection]

lemma reflection_smul {R : Type*} [CommRing R] (c : R) (φ : (Cusp × Cusp) → Binary R) :
    reflection (c • φ) = c • reflection φ := by
  funext D; simp [reflection]

lemma slash_add {R : Type*} [CommRing R] (g : Matrix (Fin 2) (Fin 2) ℤ)
    (φ ψ : (Cusp × Cusp) → Binary R) : slash g (φ + ψ) = slash g φ + slash g ψ := by
  funext D; simp [slash]

lemma slash_smul {R : Type*} [CommRing R] (g : Matrix (Fin 2) (Fin 2) ℤ) (c : R)
    (φ : (Cusp × Cusp) → Binary R) : slash g (c • φ) = c • slash g φ := by
  funext D; simp [slash]

lemma primeHecke_add {R : Type*} [CommRing R] (e : R) (l : ℕ) (φ ψ : (Cusp × Cusp) → Binary R) :
    primeHecke e l (φ + ψ) = primeHecke e l φ + primeHecke e l ψ := by
  simp only [primeHecke, slash_add, Finset.sum_add_distrib, smul_add]
  abel

lemma primeHecke_smul {R : Type*} [CommRing R] (e : R) (l : ℕ) (c : R)
    (φ : (Cusp × Cusp) → Binary R) : primeHecke e l (c • φ) = c • primeHecke e l φ := by
  simp only [primeHecke, slash_smul, ← Finset.smul_sum, smul_add, smul_comm e c]

lemma boundaryCochain_sub (Φ Ψ : Cusp → Binary ℂ) :
    boundaryCochain (Φ - Ψ) = boundaryCochain Φ - boundaryCochain Ψ := by
  funext D; simp [boundaryCochain]; abel

lemma boundaryCochain_smul (c : ℂ) (Φ : Cusp → Binary ℂ) :
    boundaryCochain (c • Φ) = c • boundaryCochain Φ := by
  funext D; simp [boundaryCochain, smul_sub]

lemma reflection_sub (φ ψ : (Cusp × Cusp) → Binary ℂ) :
    reflection (φ - ψ) = reflection φ - reflection ψ := by
  funext D; simp [reflection]

lemma IsBoundaryDatum.sub {N n : ℕ} {Φ Ψ : Cusp → Binary ℂ} (hΦ : IsBoundaryDatum N n Φ)
    (hΨ : IsBoundaryDatum N n Ψ) : IsBoundaryDatum N n (Φ - Ψ) :=
  ⟨fun x => Submodule.sub_mem _ (hΦ.1 x) (hΨ.1 x),
    fun γ x => by simp only [Pi.sub_apply, hΦ.2 γ x, hΨ.2 γ x, map_sub]⟩

lemma IsBoundaryDatum.smul {N n : ℕ} (c : ℂ) {Φ : Cusp → Binary ℂ} (hΦ : IsBoundaryDatum N n Φ) :
    IsBoundaryDatum N n (c • Φ) :=
  ⟨fun x => Submodule.smul_mem _ c (hΦ.1 x),
    fun γ x => by simp only [Pi.smul_apply, hΦ.2 γ x, map_smul]⟩

end MTT.Cohomology

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ)
    (hI : ∀ f, IntegralClass f (I f)) (hT : HeckeEquivariant I)
    (g h : CuspForm (MTT.GammaOne N) (k : ℤ)) (Φ : Cusp → Binary ℂ)
    (hΦ : IsBoundaryDatum N (k-2) Φ) (e : DirichletCharacter ℂ N)
    (hg : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      (I g).val (cuspAct γ.val x, cuspAct γ.val y) =
        e (γ.val 1 1 : ZMod N) • act γ.val.val ((I g).val (x, y)))
    (hh : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      reflection (I h).val (cuspAct γ.val x, cuspAct γ.val y) =
        e (γ.val 1 1 : ZMod N) • act γ.val.val (reflection (I h).val (x, y)))
    (hb : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      boundaryCochain Φ (cuspAct γ.val x, cuspAct γ.val y) =
        e (γ.val 1 1 : ZMod N) • act γ.val.val (boundaryCochain Φ (x, y)))
    (l : ℕ) (hl : l.Prime) (a : ℂ)
    (hsum : primeHecke (e (l : ZMod N)) l ((I g).val + reflection (I h).val + boundaryCochain Φ) =
      a • ((I g).val + reflection (I h).val + boundaryCochain Φ)) :
    primeHecke (e (l : ZMod N)) l (I g).val = a • (I g).val ∧
    primeHecke (e (l : ZMod N)) l (reflection (I h).val) = a • reflection (I h).val ∧
    primeHecke (e (l : ZMod N)) l (boundaryCochain Φ) = a • boundaryCochain Φ := by
  -- the nebentype laws of `g` and `h` as forms
  have hglaw := MTT.Cohomology.character_law_of_class hN hk I hI e g hg
  obtain ⟨ψ, hψ⟩ := (MTT.Cohomology.reflection_class (I h)).1
  have hψlaw : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      ψ.val (cuspAct γ.val x, cuspAct γ.val y) =
        e (γ.val 1 1 : ZMod N) • act γ.val.val (ψ.val (x, y)) := by
    intro γ x y; rw [hψ]; exact hh γ x y
  have hhlaw' : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      (I h).val (cuspAct γ.val x, cuspAct γ.val y) =
        e (γ.val 1 1 : ZMod N) • act γ.val.val ((I h).val (x, y)) := by
    intro γ x y
    have h1 := (MTT.Cohomology.reflection_class ψ).2.2 e hψlaw γ x y
    rwa [hψ, MTT.Cohomology.reflection_involutive] at h1
  have hhlaw := MTT.Cohomology.character_law_of_class hN hk I hI e h hhlaw'
  -- the Hecke translates of `g` and `h` are cusp forms
  obtain ⟨g₁, hg₁, -⟩ := MTT.exists_cuspForm_heckePrime_pos hN (by omega) e g hglaw l hl
  obtain ⟨h₁, hh₁, -⟩ := MTT.exists_cuspForm_heckePrime_pos hN (by omega) e h hhlaw l hl
  have hTA : primeHecke (e (l : ZMod N)) l (I g).val = (I g₁).val := (hT e l hl g g₁ hg₁).symm
  have hTB : primeHecke (e (l : ZMod N)) l (reflection (I h).val) = reflection (I h₁).val := by
    rw [← (MTT.Cohomology.reflection_class (I h)).2.1, hT e l hl h h₁ hh₁]
  obtain ⟨Ψ, hΨ, hTC⟩ := MTT.Cohomology.primeHecke_boundary_datum hN hk e Φ hΦ hb l hl
  -- directness on the difference
  have hdiff : (I (g₁ - a • g)).val + reflection (I (h₁ - a • h)).val +
      boundaryCochain (Ψ - a • Φ) = 0 := by
    have h1 := hsum
    rw [primeHecke_add, primeHecke_add, hTA, hTB, hTC] at h1
    calc (I (g₁ - a • g)).val + reflection (I (h₁ - a • h)).val + boundaryCochain (Ψ - a • Φ)
        = ((I g₁).val + reflection (I h₁).val + boundaryCochain Ψ) -
            a • ((I g).val + reflection (I h).val + boundaryCochain Φ) := by
          simp only [map_sub, map_smul, Submodule.coe_sub, Submodule.coe_smul, reflection_sub,
            reflection_smul, boundaryCochain_sub, boundaryCochain_smul, smul_add]
          abel
      _ = 0 := by rw [h1, sub_self]
  obtain ⟨hg0, hh0, hΦ0⟩ := MTT.Cohomology.eichler_shimura_direct hN hk I hI (g₁ - a • g)
    (h₁ - a • h) (Ψ - a • Φ) (hΨ.sub (hΦ.smul a)) hdiff
  refine ⟨?_, ?_, ?_⟩
  · rw [hTA, sub_eq_zero.mp hg0, map_smul, Submodule.coe_smul]
  · rw [hTB, sub_eq_zero.mp hh0, map_smul, Submodule.coe_smul, reflection_smul]
  · rw [hTC]
    rw [boundaryCochain_sub, boundaryCochain_smul] at hΦ0
    exact sub_eq_zero.mp hΦ0
