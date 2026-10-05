module

public import Definitions.FLT.Def_PeriodPair_Uniformization

import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import Mathlib.Analysis.Complex.Polynomial.Basic
import Theorems.FLT.Thm_PeriodPair_jLattice_surjective
import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PeriodPair_exists_variableChange_smul_weierstrassCurve_eq

theorem solution (E : WeierstrassCurve ℂ) [E.IsElliptic] :
    ∃ (L : PeriodPair) (C : WeierstrassCurve.VariableChange ℂ), C • L.weierstrassCurve = E := by
  obtain ⟨L, hΔ, hj⟩ := PeriodPair.jLattice_surjective E.j
  have : L.weierstrassCurve.IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr hΔ.weierstrassCurve_Δ_ne_zero⟩
  have hjE : L.weierstrassCurve.j = E.j := by
    rw [← hj, L.jLattice_eq_c₄_pow_three_div_Δ, WeierstrassCurve.j, div_eq_mul_inv, mul_comm,
      Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ']
  exact ⟨L, WeierstrassCurve.exists_variableChange_of_j_eq L.weierstrassCurve E hjE⟩

end S_PeriodPair_exists_variableChange_smul_weierstrassCurve_eq
end P2MW
export P2MW.S_PeriodPair_exists_variableChange_smul_weierstrassCurve_eq (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem PeriodPair.exists_variableChange_smul_weierstrassCurve_eq (E : WeierstrassCurve ℂ) [E.IsElliptic] :
    ∃ (L : PeriodPair) (C : WeierstrassCurve.VariableChange ℂ), C • L.weierstrassCurve = E := _root_.P2MW.S_PeriodPair_exists_variableChange_smul_weierstrassCurve_eq.solution E

end publicSection
