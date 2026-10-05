module

public import Definitions.FLT.Def_LanglandsTunnell_TowerCounting
public import Mathlib.Topology.Instances.Real.Lemmas

public section publicSection

open NumberField Ideal Filter Topology

namespace FrobeniusDensity

/-- Chebotarev's density theorem over `ℚ`, stated as natural density relative to the
rational primes and allowing an arbitrary finite set of excluded residue characteristics. -/
theorem chebotarev_natural_density
    (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (σ : L ≃ₐ[ℚ] L) (S : Finset ℕ) :
    Tendsto
      (fun X : ℕ =>
        (((Finset.range X).filter fun ℓ =>
            ℓ ∉ S ∧ LanglandsTunnell.classIndicator σ ℓ = 1).card : ℝ) /
          (((Finset.range X).filter Nat.Prime).card : ℝ))
      atTop
      (𝓝 ((Nat.card {τ : L ≃ₐ[ℚ] L | IsConj σ τ} : ℝ) /
        (Nat.card (L ≃ₐ[ℚ] L) : ℝ))) := by sorry

end FrobeniusDensity

end publicSection
