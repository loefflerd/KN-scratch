module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public noncomputable section publicSection

namespace MonoidAlgebra

/-- The augmentation homomorphism from a monoid algebra to its coefficient ring. -/
def augmentation (R : Type*) [CommRing R] (G : Type*) [Group G] :
    MonoidAlgebra R G →+* R :=
  (MonoidAlgebra.lift R R G 1).toRingHom

end MonoidAlgebra

namespace ValuationSubring

/-- The subtype of a valuation subring and the subtype of its underlying
`Subring` are canonically isomorphic as rings. -/
def subtypeToSubringEquiv {K : Type*} [Field K] (A : ValuationSubring K) :
    A.toSubring ≃+* A where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

end ValuationSubring

end publicSection
