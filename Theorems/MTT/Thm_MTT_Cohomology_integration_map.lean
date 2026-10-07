module

public import Definitions.MTT.Def_MTT_Cohomology
public import Mathlib.RingTheory.Flat.Basic

import Theorems.MTT.Thm_MTT_Cohomology_integration_linear_map_exists
import Theorems.MTT.Thm_MTT_Cohomology_integration_cochain_injective
import Theorems.MTT.Thm_MTT_Cohomology_integration_cochain_hecke_equivariant
import Theorems.MTT.Thm_MTT_Cohomology_integration_cochain_integral_class

section privateSection

open MTT.Cohomology

theorem solution {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) :
    ∃ I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k - 2) ℂ,
      Function.Injective I ∧ HeckeEquivariant I ∧ ∀ f, IntegralClass f (I f) := by
  obtain ⟨I, hI⟩ := integration_linear_map_exists hN hk
  exact ⟨I,
    integration_cochain_injective hN hk I hI,
    integration_cochain_hecke_equivariant hN hk I hI,
    integration_cochain_integral_class hN hk I hI⟩

end privateSection

public section publicSection

noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.integration_map
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) :
    ∃ I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ,
      Function.Injective I ∧ HeckeEquivariant I ∧ ∀ f, IntegralClass f (I f) := _root_.solution hN hk
end

end publicSection
