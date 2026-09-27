import Mathlib
import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.FLT.Def_WeierstrassCurve_FunctionFieldQuadratic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u
theorem WeierstrassCurve.Affine.FunctionField.addX_addY_specialize_at_place
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic] [DecidableEq W.FunctionField]
    (φ₁ φ₂ : W.FunctionField →ₐ[F] W.FunctionField)
    (hcol : ¬ (φ₁ (polyToFunctionField W Polynomial.X) = φ₂ (polyToFunctionField W Polynomial.X) ∧
      φ₁ (yCoord W) = (W.map (algebraMap F W.FunctionField)).toAffine.negY
        (φ₂ (polyToFunctionField W Polynomial.X)) (φ₂ (yCoord W))))
    (hnc : ∀ c : F,
      (W.map (algebraMap F W.FunctionField)).toAffine.addX
          (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
          ((W.map (algebraMap F W.FunctionField)).toAffine.slope
            (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
            (φ₁ (yCoord W)) (φ₂ (yCoord W)))
        ≠ algebraMap F W.FunctionField c)
    (v : AlgebraicCurve.Place F W.FunctionField) (Q₁ Q₂ : W.Point)
    (h₁0 : Q₁ = 0 → φ₁ (polyToFunctionField W Polynomial.X) ∉ v.toValuationSubring)
    (h₁s : ∀ (a b : F) (h : W.Nonsingular a b), Q₁ = .some a b h →
      0 < v.ord (φ₁ (polyToFunctionField W Polynomial.X) - algebraMap F W.FunctionField a) ∧
        0 < v.ord (φ₁ (yCoord W) - algebraMap F W.FunctionField b))
    (h₂0 : Q₂ = 0 → φ₂ (polyToFunctionField W Polynomial.X) ∉ v.toValuationSubring)
    (h₂s : ∀ (a b : F) (h : W.Nonsingular a b), Q₂ = .some a b h →
      0 < v.ord (φ₂ (polyToFunctionField W Polynomial.X) - algebraMap F W.FunctionField a) ∧
        0 < v.ord (φ₂ (yCoord W) - algebraMap F W.FunctionField b)) :
    (Q₁ + Q₂ = 0 →
      (W.map (algebraMap F W.FunctionField)).toAffine.addX
          (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
          ((W.map (algebraMap F W.FunctionField)).toAffine.slope
            (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
            (φ₁ (yCoord W)) (φ₂ (yCoord W)))
        ∉ v.toValuationSubring) ∧
    (∀ (a b : F) (h : W.Nonsingular a b), Q₁ + Q₂ = .some a b h →
      0 < v.ord ((W.map (algebraMap F W.FunctionField)).toAffine.addX
          (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
          ((W.map (algebraMap F W.FunctionField)).toAffine.slope
            (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
            (φ₁ (yCoord W)) (φ₂ (yCoord W)))
        - algebraMap F W.FunctionField a) ∧
      0 < v.ord ((W.map (algebraMap F W.FunctionField)).toAffine.addY
          (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
          (φ₁ (yCoord W))
          ((W.map (algebraMap F W.FunctionField)).toAffine.slope
            (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
            (φ₁ (yCoord W)) (φ₂ (yCoord W)))
        - algebraMap F W.FunctionField b)) := by sorry
