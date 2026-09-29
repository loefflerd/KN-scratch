import Definitions.MTT.Def_MTT_Cohomology_Integration
import Mathlib.RingTheory.Flat.Basic
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

namespace MTT.Cohomology

lemma binaryExponent_apply_zero (n j : ℕ) : binaryExponent n j 0 = j := by
  simp [binaryExponent]

/-- The coefficient of `X^j Y^(k-2-j)` in the cusp period polynomial is the normalised
vertical modular integral. -/
lemma coeff_cuspPeriodPolynomial {N k : ℕ} (hk : 2 ≤ k) (f : CuspForm (MTT.GammaOne N) (k : ℤ))
    (r : ℚ) {j : ℕ} (hj : j ≤ k - 2) :
    AddMonoidAlgebra.coeff (cuspPeriodPolynomial f r) (binaryExponent (k - 2) j) =
      ((k - 2).choose j : ℂ) * MTT.modularIntegral f (Polynomial.X ^ j) r := by
  rw [cuspPeriodPolynomial, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [ite_eq_right]
    intro h
    exact hij (by simpa [binaryExponent_apply_zero] using congrArg (fun v => v 0) h)
  · intro hj'
    exact absurd (Finset.mem_range.mpr (by omega)) hj'

/-- The integration cochain at `(∞, r)` is the cusp period polynomial at `r`. -/
lemma integrationCochain_infty {N k : ℕ} (f : CuspForm (MTT.GammaOne N) (k : ℤ)) (r : ℚ) :
    integrationCochain f (OnePoint.infty, (r : Cusp)) = cuspPeriodPolynomial f r := by
  change cuspPeriodPolynomial f r - 0 = _
  rw [sub_zero]

lemma evaluation_of_integrationCochain {N k : ℕ} (hk : 2 ≤ k)
    (f : CuspForm (MTT.GammaOne N) (k : ℤ))
    (φ : Hc N (k - 2) ℂ) (hφ : φ.val = integrationCochain f) {j : ℕ} (hj : j ≤ k - 2) (r : ℚ) :
    evaluation j r φ = ((k - 2).choose j : ℂ) * MTT.modularIntegral f (Polynomial.X ^ j) r := by
  change AddMonoidAlgebra.coeff (φ.val (OnePoint.infty, (r : Cusp))) (binaryExponent (k - 2) j) = _
  rw [hφ, integrationCochain_infty]
  exact coeff_cuspPeriodPolynomial hk f r hj

end MTT.Cohomology

set_option linter.unusedVariables false in
theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ)
    (hI : ∀ f, (I f).val = integrationCochain f) :
    ∀ f, IntegralClass f (I f) := by
  intro f j r hj
  exact evaluation_of_integrationCochain hk f (I f) (hI f) hj r
