import Definitions.MTT.Def_MTT_Cohomology_Boundary
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.eichler_shimura_nebentype_compatible
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ)
    (hI : ∀ f, IntegralClass f (I f))
    (g h : CuspForm (MTT.GammaOne N) (k : ℤ)) (Φ : Cusp → Binary ℂ)
    (hΦ : IsBoundaryDatum N (k-2) Φ) (e : ZMod N → ℂ)
    (hlaw : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      ((I g).val + reflection (I h).val + boundaryCochain Φ) (cuspAct γ.val x, cuspAct γ.val y) =
        e (γ.val 1 1 : ZMod N) •
          act γ.val.val (((I g).val + reflection (I h).val + boundaryCochain Φ) (x, y))) :
    (∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      (I g).val (cuspAct γ.val x, cuspAct γ.val y) =
        e (γ.val 1 1 : ZMod N) • act γ.val.val ((I g).val (x, y))) ∧
    (∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      reflection (I h).val (cuspAct γ.val x, cuspAct γ.val y) =
        e (γ.val 1 1 : ZMod N) • act γ.val.val (reflection (I h).val (x, y))) ∧
    (∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      boundaryCochain Φ (cuspAct γ.val x, cuspAct γ.val y) =
        e (γ.val 1 1 : ZMod N) • act γ.val.val (boundaryCochain Φ (x, y))) := by sorry
