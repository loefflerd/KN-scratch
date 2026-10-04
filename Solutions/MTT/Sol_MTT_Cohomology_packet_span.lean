import Definitions.MTT.Def_MTT_Cohomology_Boundary
import Theorems.MTT.Thm_MTT_Cohomology_eichler_shimura_span
import Theorems.MTT.Thm_MTT_Cohomology_eichler_shimura_nebentype_compatible
import Theorems.MTT.Thm_MTT_Cohomology_eichler_shimura_hecke_compatible_char
import Theorems.MTT.Thm_MTT_Cohomology_image_packet_unique
import Theorems.MTT.Thm_MTT_Cohomology_boundary_packet_zero
import Theorems.MTT.Thm_MTT_Cohomology_reflection_class
import Theorems.MTT.Thm_MTT_Cohomology_reflection_involutive
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

namespace P2MPS

theorem reflection_smul {R : Type*} [CommRing R] (a : R) (φ : (Cusp × Cusp) → Binary R) :
    reflection (a • φ) = a • reflection φ := by
  funext D; simp [reflection]

end P2MPS

open P2MPS in
theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ)
    (hI : ∀ f, IntegralClass f (I f)) (hT : HeckeEquivariant I)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) (φ : Hc N (k-2) ℂ)
    (hφH : ∀ l : ℕ, l.Prime →
      primeHecke (ι (f.epsilon (l : ZMod N))) l φ.val = ι (f.coeff l) • φ.val)
    (hφε : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      φ.val (cuspAct γ.val x, cuspAct γ.val y) =
        ι (f.epsilon (γ.val 1 1 : ZMod N)) • act γ.val.val (φ.val (x, y))) :
    ∃ c d : ℂ, φ.val = c • (I f.form).val + d • reflection (I f.form).val := by
  set e : ZMod N → ℂ := fun d => ι (f.epsilon d) with he
  obtain ⟨g, h, Φ, hΦ, hdec⟩ := MTT.Cohomology.eichler_shimura_span hN hk I hI φ
  -- the nebentype law passes to the three summands
  have hlaw : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      ((I g).val + reflection (I h).val + boundaryCochain Φ) (cuspAct γ.val x, cuspAct γ.val y) =
        e (γ.val 1 1 : ZMod N) •
          act γ.val.val (((I g).val + reflection (I h).val + boundaryCochain Φ) (x, y)) := by
    intro γ x y; rw [← hdec]; exact hφε γ x y
  obtain ⟨hg, hh, hb⟩ :=
    MTT.Cohomology.eichler_shimura_nebentype_compatible hN hk I hI g h Φ hΦ e hlaw
  -- the Hecke equations pass to the three summands
  have hH : ∀ l : ℕ, l.Prime →
      primeHecke (e (l : ZMod N)) l (I g).val = ι (f.coeff l) • (I g).val ∧
      primeHecke (e (l : ZMod N)) l (reflection (I h).val) = ι (f.coeff l) • reflection (I h).val ∧
      primeHecke (e (l : ZMod N)) l (boundaryCochain Φ) = ι (f.coeff l) • boundaryCochain Φ := by
    intro l hl
    refine MTT.Cohomology.eichler_shimura_hecke_compatible_char hN hk I hI hT g h Φ hΦ
      (f.epsilon.ringHomComp ι) hg hh hb
      l hl (ι (f.coeff l)) ?_
    rw [← hdec]; exact hφH l hl
  -- the holomorphic summand
  obtain ⟨c, hc⟩ := MTT.Cohomology.image_packet_unique hN hk I hI hT ι f g hg
    (fun l hl => (hH l hl).1)
  -- the antiholomorphic summand: pull the equations back through the involution
  have hh' : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      (I h).val (cuspAct γ.val x, cuspAct γ.val y) =
        e (γ.val 1 1 : ZMod N) • act γ.val.val ((I h).val (x, y)) := by
    obtain ⟨ψ, hψ⟩ := (MTT.Cohomology.reflection_class (I h)).1
    have := (MTT.Cohomology.reflection_class ψ).2.2 e (by rw [hψ]; exact hh)
    rw [hψ, MTT.Cohomology.reflection_involutive] at this
    exact this
  have hH' : ∀ l : ℕ, l.Prime →
      primeHecke (e (l : ZMod N)) l (I h).val = ι (f.coeff l) • (I h).val := by
    intro l hl
    have h1 := (hH l hl).2.1
    have hcomm := (MTT.Cohomology.reflection_class (I h)).2.1 (e (l : ZMod N)) l
    -- reflection (primeHecke (I h)) = primeHecke (reflection (I h)) = a • reflection (I h)
    have h2 : reflection (primeHecke (e (l : ZMod N)) l (I h).val) =
        reflection (ι (f.coeff l) • (I h).val) := by
      rw [hcomm, h1, reflection_smul]
    have h3 := congrArg reflection h2
    simpa [MTT.Cohomology.reflection_involutive] using h3
  obtain ⟨d, hd⟩ := MTT.Cohomology.image_packet_unique hN hk I hI hT ι f h hh' hH'
  -- the boundary summand vanishes
  have hb0 : boundaryCochain Φ = 0 :=
    MTT.Cohomology.boundary_packet_zero hN hk ι f Φ hΦ hb (fun l hl => (hH l hl).2.2)
  refine ⟨c, d, ?_⟩
  rw [hdec, hb0, hc, hd, map_smul, map_smul, add_zero]
  simp [reflection_smul]
