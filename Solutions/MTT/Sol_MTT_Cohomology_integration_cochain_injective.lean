import Theorems.MTT.Thm_MTT_period_vanishing
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
    MvPolynomial.coeff (binaryExponent (k - 2) j) (cuspPeriodPolynomial f r) =
      ((k - 2).choose j : ℂ) * MTT.modularIntegral f (Polynomial.X ^ j) r := by
  rw [cuspPeriodPolynomial, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [if_neg]
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
  change MvPolynomial.coeff (binaryExponent (k - 2) j) (φ.val (OnePoint.infty, (r : Cusp))) = _
  rw [hφ, integrationCochain_infty]
  exact coeff_cuspPeriodPolynomial hk f r hj

end MTT.Cohomology

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ)
    (hI : ∀ f, (I f).val = integrationCochain f) :
    Function.Injective I := by
  intro f g hfg
  have h0 : I (f - g) = 0 := by rw [map_sub, hfg, sub_self]
  have hval : integrationCochain (f - g) = 0 := by rw [← hI (f - g), h0]; rfl
  have hzero : f - g = 0 := MTT.period_vanishing hN hk (f - g) (fun j hj r => by
    have h1 : cuspPeriodPolynomial (f - g) r = 0 := by
      rw [← integrationCochain_infty, hval]; rfl
    have h2 := coeff_cuspPeriodPolynomial hk (f - g) r hj
    rw [h1, MvPolynomial.coeff_zero] at h2
    have hch : (((k - 2).choose j : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj).ne'
    exact (mul_eq_zero.mp h2.symm).resolve_left hch)
  exact sub_eq_zero.mp hzero
