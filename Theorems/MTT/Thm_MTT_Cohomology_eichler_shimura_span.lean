import Definitions.MTT.Def_MTT_Cohomology_Boundary
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.eichler_shimura_span
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ)
    (hI : ∀ f, IntegralClass f (I f)) (φ : Hc N (k-2) ℂ) :
    ∃ (g h : CuspForm (MTT.GammaOne N) (k : ℤ)) (Φ : Cusp → Binary ℂ),
      IsBoundaryDatum N (k-2) Φ ∧
      φ.val = (I g).val + reflection (I h).val + boundaryCochain Φ := by sorry
