import Definitions.FLT.Def_ModularCurve_SpecialisationVocab
import Definitions.FLT.Def_ModularCurve_TatePoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve.TatePoint
open scoped Classical
theorem ModularCurve.B3.exists_torsionBy_reduction_addEquiv (W : WeierstrassCurve H)
    [W.IsElliptic] (hW : IntegralCoeffs W) (hΔ : W.Δ.orderTop = 0)
    [(specialFibre W).IsElliptic] (p : ℕ) [Fact p.Prime] :
    ∃ e : Submodule.torsionBy ℤ W.toAffine.Point (p : ℤ) ≃+
        Submodule.torsionBy ℤ (specialFibre W).toAffine.Point (p : ℤ),
      ∀ (P : Submodule.torsionBy ℤ W.toAffine.Point (p : ℤ)) (x y : H)
        (h : W.toAffine.Nonsingular x y),
        (P : W.toAffine.Point) = WeierstrassCurve.Affine.Point.some x y h →
          ∃ h₀ : (specialFibre W).toAffine.Nonsingular (x.coeff 0) (y.coeff 0),
            ((e P : Submodule.torsionBy ℤ (specialFibre W).toAffine.Point (p : ℤ)) :
                (specialFibre W).toAffine.Point) =
              WeierstrassCurve.Affine.Point.some (x.coeff 0) (y.coeff 0) h₀ := by sorry
