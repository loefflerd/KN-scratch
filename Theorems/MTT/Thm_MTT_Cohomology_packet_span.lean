import Definitions.MTT.Def_MTT_Cohomology
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.packet_span
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ)
    (hI : ∀ f, IntegralClass f (I f)) (hT : HeckeEquivariant I)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) (φ : Hc N (k-2) ℂ)
    (hφH : ∀ l : ℕ, l.Prime →
      primeHecke (ι (f.epsilon (l : ZMod N))) l φ.val = ι (f.coeff l) • φ.val)
    (hφε : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      φ.val (cuspAct γ.val x, cuspAct γ.val y) =
        ι (f.epsilon (γ.val 1 1 : ZMod N)) • act γ.val.val (φ.val (x, y))) :
    ∃ c d : ℂ, φ.val = c • (I f.form).val + d • reflection (I f.form).val := by sorry
