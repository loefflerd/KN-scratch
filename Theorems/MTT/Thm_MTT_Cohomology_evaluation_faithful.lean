import Definitions.MTT.Def_MTT_Cohomology
noncomputable section
open scoped BigOperators
open MTT.Cohomology

theorem MTT.Cohomology.evaluation_faithful
    {N n : ℕ} {R : Type*} [CommRing R] (φ ψ : Hc N n R)
    (h : ∀ j r, j ≤ n → evaluation j r φ = evaluation j r ψ) :
    φ = ψ := by sorry
