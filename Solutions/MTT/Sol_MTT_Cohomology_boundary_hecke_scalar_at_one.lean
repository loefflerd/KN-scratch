import Theorems.MTT.Thm_MTT_Cohomology_boundary_hecke_cusp_sum_at_one
import Definitions.MTT.Def_MTT_Cohomology_Boundary
import Mathlib.NumberTheory.LSeries.PrimesInAP

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open MTT.Cohomology

theorem solution
    {N n : ℕ} (hN : 0 < N)
    (Φ : Cusp → Binary ℂ) (hΦ : IsBoundaryDatum N n Φ)
    (l : ℕ) (hl : l.Prime) (hlN : (l : ZMod N) = 1) :
    primeHecke (1 : ℂ) l (boundaryCochain Φ) =
      ((1 + l^(n+1) : ℕ) : ℂ) • boundaryCochain Φ := by
  classical
  funext D
  simp only [primeHecke, Pi.add_apply, Finset.sum_apply, one_smul,
    slash, boundaryCochain, map_sub]
  rw [Finset.sum_sub_distrib]
  have hy := MTT.Cohomology.boundary_hecke_cusp_sum_at_one
    hN Φ hΦ l hl hlN D.2
  have hx := MTT.Cohomology.boundary_hecke_cusp_sum_at_one
    hN Φ hΦ l hl hlN D.1
  calc
    (∑ x : Fin l,
        act (Matrix.adjugate !![1, (x.val : ℤ); 0, (l : ℤ)])
          (Φ (fractional !![1, (x.val : ℤ); 0, (l : ℤ)] D.2))) -
        (∑ x : Fin l,
          act (Matrix.adjugate !![1, (x.val : ℤ); 0, (l : ℤ)])
            (Φ (fractional !![1, (x.val : ℤ); 0, (l : ℤ)] D.1))) +
        (act (Matrix.adjugate !![(l : ℤ), 0; 0, 1])
            (Φ (fractional !![(l : ℤ), 0; 0, 1] D.2)) -
          act (Matrix.adjugate !![(l : ℤ), 0; 0, 1])
            (Φ (fractional !![(l : ℤ), 0; 0, 1] D.1))) =
      ((∑ x : Fin l,
          act (Matrix.adjugate !![1, (x.val : ℤ); 0, (l : ℤ)])
            (Φ (fractional !![1, (x.val : ℤ); 0, (l : ℤ)] D.2))) +
          act (Matrix.adjugate !![(l : ℤ), 0; 0, 1])
            (Φ (fractional !![(l : ℤ), 0; 0, 1] D.2))) -
        ((∑ x : Fin l,
          act (Matrix.adjugate !![1, (x.val : ℤ); 0, (l : ℤ)])
            (Φ (fractional !![1, (x.val : ℤ); 0, (l : ℤ)] D.1))) +
          act (Matrix.adjugate !![(l : ℤ), 0; 0, 1])
            (Φ (fractional !![(l : ℤ), 0; 0, 1] D.1))) := by abel
    _ = ((1 + l^(n+1) : ℕ) : ℂ) • Φ D.2 -
        ((1 + l^(n+1) : ℕ) : ℂ) • Φ D.1 := by rw [hy, hx]
    _ = ((1 + l^(n+1) : ℕ) : ℂ) • (Φ D.2 - Φ D.1) := by
      rw [smul_sub]
