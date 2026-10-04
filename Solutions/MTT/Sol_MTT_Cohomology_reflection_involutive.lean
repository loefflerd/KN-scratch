import Definitions.MTT.Def_MTT_Cohomology
noncomputable section
open scoped BigOperators
open MTT.Cohomology

namespace P2MRefl

/-- The fractional-linear action of `diag(-1,1)` on cusps is an involution. -/
theorem fractional_refl_refl (x : Cusp) :
    fractional !![-1, 0; 0, 1] (fractional !![-1, 0; 0, 1] x) = x := by
  cases x <;> simp [fractional, OnePoint.infty] <;> rfl

/-- The coefficient action of `diag(-1,1)` on binary polynomials is an involution. -/
theorem act_refl_refl {R : Type*} [CommRing R] (P : Binary R) :
    act !![-1, 0; 0, 1] (act !![-1, 0; 0, 1] P) = P := by
  simp only [act, AlgHom.toLinearMap_apply]
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  convert MvPolynomial.aeval_X_left_apply P using 2
  congr 1
  funext i
  fin_cases i <;> simp [Fin.sum_univ_two]

end P2MRefl

open P2MRefl in
theorem solution {R : Type*} [CommRing R]
    (φ : (Cusp × Cusp) → Binary R) : reflection (reflection φ) = φ := by
  funext D
  simp only [reflection, fractional_refl_refl]
  exact act_refl_refl _
