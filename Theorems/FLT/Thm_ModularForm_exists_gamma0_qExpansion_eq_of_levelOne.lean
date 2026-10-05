module

public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.RingTheory.LaurentSeries

import Theorems.FLT.Thm_ModularForm_exists_degeneracy_Gamma0
import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_gamma0_qExpansion_eq_of_levelOne

open UpperHalfPlane
open scoped MatrixGroups

namespace SolRESTRAux

private theorem gamma0_one_eq_top : CongruenceSubgroup.Gamma0 1 = ⊤ := by
  ext A
  simp [CongruenceSubgroup.Gamma0_mem, eq_iff_true_of_subsingleton]

private theorem gamma0_one_coe :
    ((CongruenceSubgroup.Gamma0 1 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  simp [gamma0_one_eq_top, MonoidHom.range_eq_map]

private theorem heckeDiagMatrix_one : ModularForm.heckeDiagMatrix 1 = 1 := by
  apply Units.ext
  simp [Matrix.one_fin_two]

end SolRESTRAux

theorem solution (N : ℕ) [NeZero N] {k : ℤ} (F : ModularForm 𝒮ℒ k) :
    ∃ G : ModularForm (CongruenceSubgroup.Gamma0 N) k, (G : ℍ → ℂ) = (F : ℍ → ℂ) := by
  obtain ⟨G, hG⟩ := ModularForm.exists_degeneracy_Gamma0 (show 1 * 1 ∣ N by simp)
    (ModularForm.mcast rfl F SolRESTRAux.gamma0_one_coe)
  refine ⟨G, ?_⟩
  rw [hG, SolRESTRAux.heckeDiagMatrix_one]
  funext τ
  rw [one_smul]
  rfl

end S_ModularForm_exists_gamma0_qExpansion_eq_of_levelOne
end P2MW
export P2MW.S_ModularForm_exists_gamma0_qExpansion_eq_of_levelOne (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups
theorem ModularForm.exists_gamma0_qExpansion_eq_of_levelOne (N : ℕ) [NeZero N] {k : ℤ} (F : ModularForm 𝒮ℒ k) : ∃ G : ModularForm (CongruenceSubgroup.Gamma0 N) k, (G : ℍ → ℂ) = (F : ℍ → ℂ) := _root_.P2MW.S_ModularForm_exists_gamma0_qExpansion_eq_of_levelOne.solution N F

end publicSection
