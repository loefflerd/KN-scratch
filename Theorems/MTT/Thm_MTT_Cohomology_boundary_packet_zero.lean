module

public import Definitions.MTT.Def_MTT_Cohomology_Boundary

import Theorems.MTT.Thm_MTT_Cohomology_boundary_hecke_scalar_at_one
import Theorems.MTT.Thm_MTT_cusp_log_weighted_square_summable
import Mathlib.NumberTheory.LSeries.PrimesInAP

section privateSection

noncomputable section
open scoped BigOperators
open MTT.Cohomology

private theorem close_boundary_packet
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (Φ : Cusp → Binary ℂ) (_hΦ : IsBoundaryDatum N (k-2) Φ)
    (hH : ∀ l : ℕ, l.Prime →
      primeHecke (ι (f.epsilon (l : ZMod N))) l (boundaryCochain Φ) =
        ι (f.coeff l) • boundaryCochain Φ)
    (hscalar : ∀ l : ℕ, l.Prime → (l : ZMod N) = 1 →
      primeHecke (1 : ℂ) l (boundaryCochain Φ) =
        ((1 + l^(k-1) : ℕ) : ℂ) • boundaryCochain Φ)
    (hsum : Summable fun m : ℕ =>
      ‖ι (f.coeff m)‖^2 * Real.log m / (m : ℝ)^(k+1)) :
    boundaryCochain Φ = 0 := by
  have : NeZero N := ⟨Nat.ne_of_gt hN⟩
  by_contra hne
  have heigen (l : ℕ) (hl : l.Prime) (hlN : (l : ZMod N) = 1) :
      ι (f.coeff l) = ((1 + l^(k-1) : ℕ) : ℂ) := by
    have h := hH l hl
    rw [hlN, map_one, map_one, hscalar l hl hlN] at h
    exact (smul_left_injective ℂ hne) h.symm
  apply ArithmeticFunction.vonMangoldt.not_summable_residueClass_prime_div
    (a := (1 : ZMod N)) isUnit_one
  apply Summable.of_nonneg_of_le _ _ hsum
  · intro m
    exact div_nonneg (by split_ifs; exact ArithmeticFunction.vonMangoldt.residueClass_nonneg _ _; rfl) (Nat.cast_nonneg _)
  · intro m
    by_cases hm : m.Prime
    · by_cases hmN : (m : ZMod N) = 1
      · simp only [hm, ite_true, ArithmeticFunction.vonMangoldt.residueClass,
          Set.indicator_apply, Set.mem_ofPred_eq, hmN, ite_true, ArithmeticFunction.vonMangoldt_apply_prime hm]
        rw [heigen m hm hmN, Complex.norm_natCast, Nat.cast_add, Nat.cast_one, Nat.cast_pow]
        have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm.pos
        have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.one_lt.le
        have hp : (m : ℝ)^k ≤ (1 + (m : ℝ)^(k-1))^2 := by
          calc
            (m : ℝ)^k ≤ (m : ℝ)^(2*(k-1)) := pow_le_pow_right₀ hm1 (by omega)
            _ = ((m : ℝ)^(k-1))^2 := by rw [mul_comm 2, pow_mul]
            _ ≤ (1 + (m : ℝ)^(k-1))^2 := by nlinarith [pow_nonneg hm0.le (k-1)]
        rw [div_le_div_iff₀ hm0 (pow_pos hm0 _), pow_succ]
        calc
          Real.log (m : ℝ) * ((m : ℝ)^k * m) = (m : ℝ)^k * Real.log m * m := by ring
          _ ≤ (1 + (m : ℝ)^(k-1))^2 * Real.log m * m := by gcongr
      · simp only [hm, ite_true, ArithmeticFunction.vonMangoldt.residueClass,
          Set.indicator_apply, Set.mem_ofPred_eq, hmN, ite_false, zero_div]
        exact div_nonneg (mul_nonneg (sq_nonneg _) (Real.log_nonneg (by exact_mod_cast hm.one_lt.le))) (pow_nonneg (Nat.cast_nonneg _) _)
    · simp only [hm, ite_false, zero_div]
      by_cases hm0 : m = 0
      · subst m; simp
      · exact div_nonneg (mul_nonneg (sq_nonneg _) (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm0))) (pow_nonneg (Nat.cast_nonneg _) _)

set_option linter.unusedVariables false in
theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (Φ : Cusp → Binary ℂ) (hΦ : IsBoundaryDatum N (k-2) Φ)
    (hlaw : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      boundaryCochain Φ (cuspAct γ.val x, cuspAct γ.val y) =
        ι (f.epsilon (γ.val 1 1 : ZMod N)) • act γ.val.val (boundaryCochain Φ (x, y)))
    (hH : ∀ l : ℕ, l.Prime →
      primeHecke (ι (f.epsilon (l : ZMod N))) l (boundaryCochain Φ) =
        ι (f.coeff l) • boundaryCochain Φ) :
    boundaryCochain Φ = 0  := by
  apply close_boundary_packet hN hk ι f Φ hΦ hH
  · intro l hl hlN
    have h := MTT.Cohomology.boundary_hecke_scalar_at_one hN Φ hΦ l hl hlN
    have hk' : k-2+1 = k-1 := by omega
    simpa only [hk'] using h
  · simpa only [f.coeff_eq] using MTT.cusp_log_weighted_square_summable hN hk f.form
end

end privateSection

public section publicSection

noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.boundary_packet_zero
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (Φ : Cusp → Binary ℂ) (hΦ : IsBoundaryDatum N (k-2) Φ)
    (hlaw : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      boundaryCochain Φ (cuspAct γ.val x, cuspAct γ.val y) =
        ι (f.epsilon (γ.val 1 1 : ZMod N)) • act γ.val.val (boundaryCochain Φ (x, y)))
    (hH : ∀ l : ℕ, l.Prime →
      primeHecke (ι (f.epsilon (l : ZMod N))) l (boundaryCochain Φ) =
        ι (f.coeff l) • boundaryCochain Φ) :
    boundaryCochain Φ = 0 := _root_.solution hN hk ι f Φ hΦ hlaw hH
end

end publicSection
