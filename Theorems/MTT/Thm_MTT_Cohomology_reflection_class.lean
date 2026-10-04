import Definitions.MTT.Def_MTT_Cohomology
import Mathlib.RingTheory.Flat.Basic
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.reflection_class {N n : ℕ} {R : Type*} [CommRing R] (φ : Hc N n R) :
    (∃ ψ : Hc N n R, ψ.val = reflection φ.val) ∧
    (∀ (e : R) (l : ℕ), reflection (primeHecke e l φ.val)
        = primeHecke e l (reflection φ.val)) ∧
    (∀ (e : ZMod N → R),
      (∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
        φ.val (cuspAct γ.val x, cuspAct γ.val y)
          = e (γ.val 1 1 : ZMod N) • act γ.val.val (φ.val (x, y))) →
      ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
        reflection φ.val (cuspAct γ.val x, cuspAct γ.val y)
          = e (γ.val 1 1 : ZMod N) • act γ.val.val (reflection φ.val (x, y))) := by sorry
