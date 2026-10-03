module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

import Mathlib.RingTheory.MvPolynomial.EulerIdentity

section privateSection

namespace MvPolynomial
namespace DegAux
open MvPolynomial

open MvPolynomial

theorem isHomogeneous_iterate_pderiv
    {σ R : Type*} [CommSemiring R] {φ : MvPolynomial σ R} {n : ℕ} (k : σ)
    (hφ : φ.IsHomogeneous n) (j : ℕ) : ((pderiv k)^[j] φ).IsHomogeneous (n - j) := by
  induction j with
  | zero => simpa using hφ
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    simpa [Nat.sub_sub] using ih.pderiv

theorem iterate_pderiv_eq_zero_of_lt {σ R : Type*} [CommSemiring R] {φ : MvPolynomial σ R} {n : ℕ}
    (hφ : φ.IsHomogeneous n) (k : σ) {i : ℕ} (hi : n < i) : (pderiv k)^[i] φ = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hi
  rw [show n + m + 1 = m + 1 + n by ring, Function.iterate_add_apply,
    Function.iterate_succ_apply]
  have h0 : ((pderiv k)^[n] φ).IsHomogeneous 0 := by
    simpa using isHomogeneous_iterate_pderiv k hφ n
  have hC : (pderiv k)^[n] φ = C (AddMonoidAlgebra.coeff ((pderiv k)^[n] φ) 0) :=
    totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero h0.totalDegree_le)
  rw [hC, pderiv_C]
  exact Function.iterate_fixed (map_zero _) m

end MvPolynomial.DegAux

theorem solution {σ R : Type*} [CommSemiring R] {φ : MvPolynomial σ R}
    {n : ℕ} (hφ : φ.IsHomogeneous n) (k : σ) {i : ℕ} (hi : n < i) :
    (MvPolynomial.pderiv k)^[i] φ = 0 :=
  MvPolynomial.DegAux.iterate_pderiv_eq_zero_of_lt hφ k hi

end privateSection

public section publicSection

theorem MvPolynomial.IsHomogeneous.iterate_pderiv_eq_zero_of_lt
    {σ R : Type*} [CommSemiring R] {φ : MvPolynomial σ R}
    {n : ℕ} (hφ : φ.IsHomogeneous n) (k : σ) {i : ℕ} (hi : n < i) :
    (MvPolynomial.pderiv k)^[i] φ = 0 := by
  exact solution hφ k hi

end publicSection
