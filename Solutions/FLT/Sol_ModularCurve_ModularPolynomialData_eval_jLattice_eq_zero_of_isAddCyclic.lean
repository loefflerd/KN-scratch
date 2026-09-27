import Mathlib
import Definitions.FLT.Def_ModularCurve_X0
import Definitions.FLT.Def_ModularCurve_PrimCosetReps
import Definitions.FLT.Def_PeriodPair_Uniformization
import Theorems.FLT.Thm_PeriodPair_exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic
import Theorems.FLT.Thm_PeriodPair_jLattice_ofTau
import Theorems.FLT.Thm_ModularCurve_ModularPolynomialData_eval_E4_cube_div_discriminant_coset_eq_zero
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_eval_jLattice_eq_zero_of_isAddCyclic
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open UpperHalfPlane

theorem solution
    (N : ℕ) [NeZero N] (data : ModularCurve.ModularPolynomialData N) (L L' : PeriodPair)
    (hsub : (L'.lattice : Set ℂ) ⊆ L.lattice) (hidx : PeriodPair.sublatticeIndex L L' = N)
    (hcyc : IsAddCyclic (PeriodPair.sublatticeQuotient L L')) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ℂ) L.jLattice)).eval L'.jLattice = 0 := by
  obtain ⟨a, b, d, τ, σ, habd, hσ, hjL, hjL'⟩ :=
    PeriodPair.exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic L L' hsub hidx hcyc
  rw [hjL, hjL', PeriodPair.jLattice_ofTau, PeriodPair.jLattice_ofTau]
  exact ModularCurve.ModularPolynomialData.eval_E4_cube_div_discriminant_coset_eq_zero
    N data habd τ σ hσ

end S_ModularCurve_ModularPolynomialData_eval_jLattice_eq_zero_of_isAddCyclic
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_eval_jLattice_eq_zero_of_isAddCyclic (solution)
