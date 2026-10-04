import Mathlib
import Definitions.FLT.Def_ModularCurve_X1
import Definitions.FLT.Def_ModularCurve_JqCoeff
import Definitions.FLT.Def_ModularCurve_LaurentCoeff
import Definitions.FLT.Def_ModularCurve_QExpansionDiff
import Definitions.FLT.Def_AlgebraicCurve_Repartitions
import Definitions.FLT.Def_ModularCurve_ComplexPlaceDictionaryOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CongruenceSubgroup ModularCurve
open scoped MatrixGroups ModularForm
theorem ModularCurve.exists_tendsto_realizeOf_mul_exp_of_not_mem_toValuationSubring
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (y : ↥(ModularCurve.laurentBaseChange ℂ F₀)) (hy : (y : LaurentSeries ℂ) = ModularCurve.jqModC ℂ)
    (hdeg : Module.finrank
        ↥(IntermediateField.adjoin ℂ ({y} : Set ↥(ModularCurve.laurentBaseChange ℂ F₀)))
        ↥(ModularCurve.laurentBaseChange ℂ F₀) =
      (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index)
    (P : AlgebraicCurve.Place ℂ ↥(ModularCurve.laurentBaseChange ℂ F₀)) (hP : y ∉ P.toValuationSubring) :
    ∃ (σ : SL(2, ℤ)) (h : ℕ), 0 < h ∧
      σ * ModularGroup.T ^ h * σ⁻¹ ∈ Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) ∧
      P.ord y = -(h : ℤ) ∧
      ∀ x : ↥(ModularCurve.laurentBaseChange ℂ F₀), x ≠ 0 → ∃ L : ℂ, L ≠ 0 ∧
        Filter.Tendsto
          (fun τ : UpperHalfPlane => ModularCurve.realizeOf Γ (x : LaurentSeries ℂ) (σ • τ) *
            Complex.exp (-(2 * Real.pi * Complex.I * (P.ord x : ℂ) * (τ : ℂ) / (h : ℂ))))
          UpperHalfPlane.atImInfty (nhds L) := by sorry
