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
theorem ModularCurve.neg_width_le_ord_of_order_eq_mul_ord_of_qExpansion_slash
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (y : ↥(ModularCurve.laurentBaseChange ℂ F₀))
    (σ : SL(2, ℤ))
    (Φ : ModularCurve.laurentBaseChange ℂ F₀ →+* LaurentSeries ℂ)
    (P : AlgebraicCurve.Place ℂ (ModularCurve.laurentBaseChange ℂ F₀)) (e : ℕ) (he : 0 < e)
    (hpres : ∀ (x : ModularCurve.laurentBaseChange ℂ F₀) (k : ℤ)
          (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k), h ≠ 0 →
        (x : LaurentSeries ℂ) *
            ((UpperHalfPlane.qExpansion 1 (h : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
          ((UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) →
        Φ x * ((UpperHalfPlane.qExpansion (Γ.normalCore.index : ℝ)
              ((h : UpperHalfPlane → ℂ) ∣[k] σ) : PowerSeries ℂ) : LaurentSeries ℂ) =
          ((UpperHalfPlane.qExpansion (Γ.normalCore.index : ℝ)
              ((g : UpperHalfPlane → ℂ) ∣[k] σ) : PowerSeries ℂ) : LaurentSeries ℂ))
    (hord : ∀ x : ModularCurve.laurentBaseChange ℂ F₀, x ≠ 0 → (Φ x).order = e * P.ord x)
    (hyo : (Φ y).order = -(Γ.normalCore.index : ℤ))
    (h : ℕ) (hh : 0 < h) (hmem : σ * ModularGroup.T ^ h * σ⁻¹ ∈ Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) :
    -(h : ℤ) ≤ P.ord y := by sorry
