import Definitions.FLT.Def_ModularCurve_X0
import Definitions.FLT.Def_ModularCurve_LaurentCoeff
import Definitions.FLT.Def_ModularCurve_QAdicPlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.isRoot_map_Phi_apply_jBar (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N) (A : Type*) [CommRing A] [Algebra L A]
    (φ : laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L] A) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom A)
      (φ ⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (jq_mem_full N)⟩))).IsRoot
      (φ ⟨coeffEmb L (qExpand ℚ N jq),
        coeffEmb_mem_laurentBaseChange L (jqd_mem_full N (dvd_refl N))⟩) := by sorry
