import Definitions.FLT.Def_ModularCurve_MazurStepThreeInputs
import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.FLT.Def_AlgebraicCurve_DivisorPushPull
import Definitions.FLT.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.FLT.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.FLT.Def_AlgebraicCurve_RatFuncPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
theorem ModularCurve.nonempty_equiv_place_pos_ord_algHom_integralClosure (N : ℕ) [NeZero N]
    (j₀ : AlgebraicClosure ℚ)
    (hdeg : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), w.deg = 1) :
    Nonempty ({v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) //
        0 < v.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)} ≃
      {ψ : ↥(integralClosure
            ↥(Algebra.adjoin (AlgebraicClosure ℚ)
              ({(jBar N : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)))
            (modularFunctionFieldBar N)) →ₐ[AlgebraicClosure ℚ] AlgebraicClosure ℚ //
        ψ (algebraMap
            ↥(Algebra.adjoin (AlgebraicClosure ℚ)
              ({(jBar N : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)))
            ↥(integralClosure
              ↥(Algebra.adjoin (AlgebraicClosure ℚ)
                ({(jBar N : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)))
              (modularFunctionFieldBar N))
            ⟨jBar N, Algebra.self_mem_adjoin_singleton (AlgebraicClosure ℚ)
              (jBar N : modularFunctionFieldBar N)⟩) = j₀}) := by sorry
