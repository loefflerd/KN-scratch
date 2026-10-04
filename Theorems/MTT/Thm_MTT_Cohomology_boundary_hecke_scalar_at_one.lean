import Definitions.MTT.Def_MTT_Cohomology_Boundary
import Mathlib.NumberTheory.LSeries.PrimesInAP
noncomputable section
open scoped BigOperators
open MTT.Cohomology

theorem MTT.Cohomology.boundary_hecke_scalar_at_one
    {N n : ℕ} (hN : 0 < N)
    (Φ : Cusp → Binary ℂ) (hΦ : IsBoundaryDatum N n Φ)
    (l : ℕ) (hl : l.Prime) (hlN : (l : ZMod N) = 1) :
    primeHecke (1 : ℂ) l (boundaryCochain Φ) =
      ((1 + l^(n+1) : ℕ) : ℂ) • boundaryCochain Φ := by sorry
