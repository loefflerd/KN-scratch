import Definitions.MTT.Def_MTT_Cohomology_Boundary
import Mathlib.NumberTheory.LSeries.PrimesInAP
noncomputable section
open scoped BigOperators
open MTT.Cohomology
theorem MTT.Cohomology.boundary_hecke_cusp_sum_at_one
    {N n : ℕ} (hN : 0 < N)
    (Φ : Cusp → Binary ℂ) (hΦ : IsBoundaryDatum N n Φ)
    (l : ℕ) (hl : l.Prime) (hlN : (l : ZMod N) = 1) (x : Cusp) :
    (∑ b : Fin l,
      act (Matrix.adjugate !![1, (b.val : ℤ); 0, (l : ℤ)])
        (Φ (fractional !![1, (b.val : ℤ); 0, (l : ℤ)] x))) +
      act (Matrix.adjugate !![(l : ℤ), 0; 0, 1])
        (Φ (fractional !![(l : ℤ), 0; 0, 1] x)) =
      ((1 + l^(n+1) : ℕ) : ℂ) • Φ x := by sorry
