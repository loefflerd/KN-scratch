module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Galois.Basic

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

instance AlgebraicClosure.Rat.isGalois :
    @IsGalois ℚ _ (AlgebraicClosure ℚ) _ DivisionRing.toRatAlgebra :=
  @IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) _ _

end publicSection
