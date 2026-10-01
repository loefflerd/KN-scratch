import Definitions.FLT.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IntermediateField Algebra

namespace AlgebraicCurve
theorem isCurveOver_iff_exists_transcendental_finiteDimensional {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] :
    IsCurveOver K F ↔ ∃ t : F, Transcendental K t ∧ FiniteDimensional K⟮t⟯ F ∧ Algebra.IsSeparable K⟮t⟯ F := by sorry
