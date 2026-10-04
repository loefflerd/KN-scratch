module

public import Definitions.FLT.Def_ModularCurve_X0
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpansion_E4_eq_map_eisenstein4

noncomputable section

open UpperHalfPlane Complex Filter Topology
open scoped MatrixGroups PowerSeries.WithPiTopology

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve
p2m_export "ModularCurve" "eisenstein4"
end ModularCurve

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_qExpansion_E4_eq_map_eisenstein4.ModularCurve in
theorem solution : UpperHalfPlane.qExpansion 1 ⇑ModularForm.E₄ = PowerSeries.map (Int.castRingHom ℂ) ModularCurve.eisenstein4 := by
  ext m
  rw [EisensteinSeries.E_qExpansion_coeff _ ⟨2, rfl⟩ m, PowerSeries.coeff_map, eisenstein4,
    PowerSeries.coeff_mk]
  split_ifs with hm
  · simp
  · rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four,
      ArithmeticFunction.sigma_apply]
    simp only [eq_intCast, Int.cast_mul, Int.cast_ofNat, Int.cast_sum, Int.cast_pow,
      Int.cast_natCast]
    push_cast
    ring
end

end S_ModularCurve_qExpansion_E4_eq_map_eisenstein4
end P2MW
export P2MW.S_ModularCurve_qExpansion_E4_eq_map_eisenstein4 (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.qExpansion_E4_eq_map_eisenstein4 : UpperHalfPlane.qExpansion 1 ⇑ModularForm.E₄ = PowerSeries.map (Int.castRingHom ℂ) ModularCurve.eisenstein4 := _root_.P2MW.S_ModularCurve_qExpansion_E4_eq_map_eisenstein4.solution

end publicSection
