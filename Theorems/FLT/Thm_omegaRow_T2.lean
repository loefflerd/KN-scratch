import Definitions.FLT.Def_ModularCurve_OmegaOf
import Definitions.FLT.Def_ModularCurve_EigenformIdeal
import Definitions.FLT.Def_ModularCurve_HeckeModule
import Definitions.FLT.Def_AlgebraicCurve_Differentials
import Definitions.FLT.Def_CuspForm_IntegralStructure
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane ModularCurve AlgebraicCurve
theorem omegaRow_T2 :
    coeffMap (algebraMap ℚ ℂ) (thetaL ℚ jq) *
        ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
      = -(((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 2 *
          ((qExpansion 1 (ModularForm.E₆ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) := by sorry
