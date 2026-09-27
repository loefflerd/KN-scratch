import Definitions.MTT.Def_MTT_Cohomology_Boundary
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.eichler_shimura_direct
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ)
    (hI : ∀ f, IntegralClass f (I f))
    (g h : CuspForm (MTT.GammaOne N) (k : ℤ)) (Φ : Cusp → Binary ℂ)
    (hΦ : IsBoundaryDatum N (k-2) Φ)
    (hsum : (I g).val + reflection (I h).val + boundaryCochain Φ = 0) :
    g = 0 ∧ h = 0 ∧ boundaryCochain Φ = 0 := by sorry
