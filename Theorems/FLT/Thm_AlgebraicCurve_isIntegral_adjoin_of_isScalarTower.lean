module

public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Tower

section privateSection

theorem solution {K L F : Type*} [CommRing K] [CommRing L] [CommRing F]
    [Algebra K L] [Algebra K F] [Algebra L F] [IsScalarTower K L F] {j x : F}
    (hx : IsIntegral (Algebra.adjoin K {j}) x) : IsIntegral (Algebra.adjoin L {j}) x := by
  have hsub : Algebra.adjoin K {j} ≤ Subalgebra.restrictScalars K (Algebra.adjoin L {j}) :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr
      ((Subalgebra.mem_restrictScalars K).mpr (Algebra.subset_adjoin rfl)))
  let φ' : ↥(Algebra.adjoin K {j}) →+* ↥(Algebra.adjoin L {j}) :=
    { toFun := fun a => ⟨(a : F), (Subalgebra.mem_restrictScalars K).mp (hsub a.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact IsIntegral.map_of_comp_eq φ' (RingHom.id F) (by ext a; rfl) hx

end privateSection

public section publicSection

theorem AlgebraicCurve.isIntegral_adjoin_of_isScalarTower
    {K L F : Type*} [CommRing K] [CommRing L] [CommRing F]
    [Algebra K L] [Algebra K F] [Algebra L F] [IsScalarTower K L F] {j x : F}
    (hx : IsIntegral (Algebra.adjoin K {j}) x) : IsIntegral (Algebra.adjoin L {j}) x := by
  exact solution hx

end publicSection
