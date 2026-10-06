import Definitions.FLT.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.FLT.Def_ModularCurve_JqCoeff
import Definitions.FLT.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups Topology
theorem ModularCurve.ord_eq_zero_of_not_mem_of_realizeOf_tendsto
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (x : ModularCurve.laurentBaseChange ℂ F₀)
    (F : ℍ → ℂ)
    (hFx : ∀ τ : ℍ, (fun z : ℂ => F (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => ModularCurve.realizeOf Γ (x : LaurentSeries ℂ) (ofComplex z))
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (v : AlgebraicCurve.Place ℂ (ModularCurve.laurentBaseChange ℂ F₀))
    (y : ModularCurve.laurentBaseChange ℂ F₀) (hy : (y : LaurentSeries ℂ) = ModularCurve.jqModC ℂ)
    (hv : y ∉ v.toValuationSubring) :
    v.ord x = 0 := by sorry
