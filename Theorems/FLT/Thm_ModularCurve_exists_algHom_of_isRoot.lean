import Definitions.FLT.Def_ModularCurve_X0
import Definitions.FLT.Def_ModularCurve_JqCoeff
import Definitions.FLT.Def_ModularCurve_LaurentCoeff
import Definitions.FLT.Def_ModularCurve_QAdicPlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.exists_algHom_of_isRoot (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N) {A : Type*} [Field A] [Algebra L A] (c y : A)
    (hc : Transcendental L c)
    (hy : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom A) c)).IsRoot y) :
    ∃ ψ : laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L] A,
      ψ ⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (jq_mem_full N)⟩ = c ∧
      ψ ⟨coeffEmb L (qExpand ℚ N jq),
        coeffEmb_mem_laurentBaseChange L (jqd_mem_full N (dvd_refl N))⟩ = y := by sorry
