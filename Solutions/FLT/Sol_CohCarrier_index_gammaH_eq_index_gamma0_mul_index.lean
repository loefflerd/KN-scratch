import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star

import Definitions.FLT.Def_CohCarrier_Level
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_index_gammaH_eq_index_gamma0_mul_index

open scoped MatrixGroups in

private theorem igIDX_gamma0Units_surjective (M : ℕ) [NeZero M] :
    Function.Surjective (CohCarrier.gamma0Units M) := by
  intro u
  have hAD : (((((u⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℤ) * ((u : ZMod M).val : ℤ) - 1 : ℤ) : ZMod M) = 0 := by
    simp
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hAD
  let γ : SL(2, ℤ) := ⟨!![(((u⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℤ), k; (M : ℤ), ((u : ZMod M).val : ℤ)], by
    rw [Matrix.det_fin_two_of]
    linarith⟩
  have hγ0 : γ ∈ CongruenceSubgroup.Gamma0 M := by
    rw [CongruenceSubgroup.Gamma0_mem]
    simp [γ]
  refine ⟨⟨γ, hγ0⟩, Units.ext ?_⟩
  simp only [CohCarrier.gamma0Units, MonoidHom.coe_mk, OneHom.coe_mk, CongruenceSubgroup.Gamma0Map]
  simp [γ]

open scoped MatrixGroups in

theorem solution (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) :
    (CohCarrier.GammaH M H).index = (CongruenceSubgroup.Gamma0 M).index * H.index := by
  rw [CohCarrier.GammaH, Subgroup.index_map_subtype,
    Subgroup.index_comap_of_surjective _ (igIDX_gamma0Units_surjective M), mul_comm]

end S_CohCarrier_index_gammaH_eq_index_gamma0_mul_index
end P2MW
export P2MW.S_CohCarrier_index_gammaH_eq_index_gamma0_mul_index (solution)
