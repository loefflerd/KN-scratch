import Definitions.MTT.Def_MTT_Cohomology
import Definitions.MTT.Def_MTT_Cohomology_Integration
import Mathlib.RingTheory.Flat.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.MTT.Thm_MTT_Cohomology_cuspPrimitive_slash_relation
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

namespace P2MCLI

variable {N n k : ℕ}

theorem deg_eq (d : Fin 2 →₀ ℕ) : d.degree = d 0 + d 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]

theorem be_apply (m j : ℕ) (i : Fin 2) :
    binaryExponent m j i = if i = 0 then j else m - j := rfl

theorem be_deg {m j : ℕ} (hj : j ≤ m) : (binaryExponent m j).degree = m := by
  rw [deg_eq, be_apply, be_apply]; simp; omega

theorem be_inj {m j j' : ℕ} (h : binaryExponent m j = binaryExponent m j') : j = j' := by
  have h0 : binaryExponent m j 0 = binaryExponent m j' 0 := by rw [h]
  simpa [be_apply] using h0

theorem eq_be (m : ℕ) (d : Fin 2 →₀ ℕ) (hd : d.degree = m) : d = binaryExponent m (d 0) := by
  rw [deg_eq] at hd
  ext i
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · rw [be_apply]; simp
  · rw [be_apply]; simp; omega

theorem hom_ext {m : ℕ} {R : Type*} [CommRing R] {P Q : Binary R}
    (hP : P.IsHomogeneous m) (hQ : Q.IsHomogeneous m)
    (h : ∀ j, j ≤ m → MvPolynomial.coeff (binaryExponent m j) P
        = MvPolynomial.coeff (binaryExponent m j) Q) : P = Q := by
  refine MvPolynomial.ext _ _ fun d => ?_
  by_cases hd : d.degree = m
  · have hle : d 0 ≤ m := by rw [deg_eq] at hd; omega
    rw [eq_be m d hd]
    exact h (d 0) hle
  · rw [hP.coeff_eq_zero hd, hQ.coeff_eq_zero hd]

theorem cpp_hom (hk : 2 ≤ k) (f : CuspForm (MTT.GammaOne N) (k : ℤ)) (r : ℚ) :
    (cuspPeriodPolynomial f r).IsHomogeneous (k - 2) := by
  rw [cuspPeriodPolynomial, ← MvPolynomial.mem_homogeneousSubmodule]
  refine Submodule.sum_mem _ fun j hj => ?_
  rw [MvPolynomial.mem_homogeneousSubmodule]
  refine MvPolynomial.isHomogeneous_monomial _ (be_deg ?_)
  have := Finset.mem_range.mp hj
  omega

theorem coeff_cpp (hk : 2 ≤ k) (f : CuspForm (MTT.GammaOne N) (k : ℤ)) (r : ℚ)
    (j : ℕ) (hj : j ≤ k - 2) :
    MvPolynomial.coeff (binaryExponent (k - 2) j) (cuspPeriodPolynomial f r)
      = ((k - 2).choose j : ℂ) * MTT.modularIntegral f (Polynomial.X ^ j) r := by
  rw [cuspPeriodPolynomial, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single j]
  · rw [MvPolynomial.coeff_monomial, if_pos rfl]
  · intro b _ hbj
    rw [MvPolynomial.coeff_monomial, if_neg]
    exact fun h => hbj (be_inj h)
  · intro hj'
    exact absurd (Finset.mem_range.mpr (by omega)) hj'

theorem diag_zero {R : Type*} [CommRing R] (φ : Hc N n R) (x : Cusp) : φ.val (x, x) = 0 := by
  have h := φ.2.2.1 x x x
  have h2 : φ.val (x, x) + φ.val (x, x) - φ.val (x, x) = 0 := by rw [h]; simp
  simpa using h2

theorem val_sub {R : Type*} [CommRing R] (φ : Hc N n R) (c a b : Cusp) :
    φ.val (a, b) = φ.val (c, b) - φ.val (c, a) := by
  have h := φ.2.2.1 c a b
  rw [← h]; ring

/-- An integral class is, path by path from the cusp at infinity, the explicit
period polynomial. -/
theorem val_infty_eq (hk : 2 ≤ k) (f : CuspForm (MTT.GammaOne N) (k : ℤ))
    (φ : Hc N (k - 2) ℂ) (hφ : IntegralClass f φ) (y : Cusp) :
    φ.val (OnePoint.infty, y) = cuspPrimitive f y := by
  induction y using OnePoint.rec with
  | infty => exact diag_zero φ _
  | coe r =>
      show φ.val (OnePoint.infty, ((r : ℚ) : Cusp)) = cuspPeriodPolynomial f r
      refine hom_ext ((MvPolynomial.mem_homogeneousSubmodule _ _).mp (φ.2.1 _ _))
        (cpp_hom hk f r) fun j hj => ?_
      rw [coeff_cpp hk f r j hj]
      exact hφ j r hj

theorem mi_smul (c : ℂ) (f : CuspForm (MTT.GammaOne N) (k : ℤ)) (P : Polynomial ℂ) (r : ℚ) :
    MTT.modularIntegral ((c • f : CuspForm (MTT.GammaOne N) (k : ℤ)) : UpperHalfPlane → ℂ) P r
      = c * MTT.modularIntegral f P r := by
  have hpt : ∀ t : ℝ,
      ((c • f : CuspForm (MTT.GammaOne N) (k : ℤ)) : UpperHalfPlane → ℂ)
          (UpperHalfPlane.ofComplex ((r : ℂ) + Complex.I * t)) *
        P.eval ((r : ℂ) + Complex.I * t)
        = c * (f (UpperHalfPlane.ofComplex ((r : ℂ) + Complex.I * t)) *
            P.eval ((r : ℂ) + Complex.I * t)) := by
    intro t
    show (c * f _) * _ = _
    ring
  unfold MTT.modularIntegral
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_const_mul]
  ring

theorem cpp_smul (c : ℂ) (f : CuspForm (MTT.GammaOne N) (k : ℤ)) (r : ℚ) :
    cuspPeriodPolynomial (c • f) r = c • cuspPeriodPolynomial f r := by
  rw [cuspPeriodPolynomial, cuspPeriodPolynomial, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mi_smul, MvPolynomial.smul_monomial]
  congr 1
  ring

theorem cuspPrimitive_smul (c : ℂ) (f : CuspForm (MTT.GammaOne N) (k : ℤ)) (x : Cusp) :
    cuspPrimitive (c • f) x = c • cuspPrimitive f x := by
  induction x using OnePoint.rec with
  | infty => show (0 : Binary ℂ) = c • (0 : Binary ℂ); rw [smul_zero]
  | coe r => exact cpp_smul c f r

end P2MCLI

open P2MCLI in
theorem solution {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (φ : Hc N (k-2) ℂ) (hφ : IntegralClass f.form φ)
    (γ : CongruenceSubgroup.Gamma0 N) (r : ℚ) :
    φ.val (cuspAct γ.val OnePoint.infty, cuspAct γ.val ((r : ℚ) : Cusp))
      = ι (f.epsilon (γ.val 1 1 : ZMod N)) •
          act γ.val.val (φ.val (OnePoint.infty, ((r : ℚ) : Cusp))) := by
  set c : ℂ := ι (f.epsilon (γ.val 1 1 : ZMod N)) with hc
  have hg' : ∀ z : UpperHalfPlane,
      f.form ((Matrix.SpecialLinearGroup.mapGL ℝ γ.val) • z) =
        (((γ.val 1 0 : ℤ) : ℂ) * z + ((γ.val 1 1 : ℤ) : ℂ)) ^ k *
          ((c • f.form : CuspForm (MTT.GammaOne N) (k : ℤ)) : UpperHalfPlane → ℂ) z := by
    intro z
    rw [f.character_law γ z]
    show _ = _ * (c * f.form z)
    ring
  have hslash := MTT.Cohomology.cuspPrimitive_slash_relation hN hk f.form
    (c • f.form) γ hg' ((r : ℚ) : Cusp)
  rw [val_sub φ OnePoint.infty (cuspAct γ.val OnePoint.infty) (cuspAct γ.val ((r : ℚ) : Cusp)),
    val_infty_eq hk f.form φ hφ, val_infty_eq hk f.form φ hφ, val_infty_eq hk f.form φ hφ,
    hslash, cuspPrimitive_smul, map_smul]
  ring
