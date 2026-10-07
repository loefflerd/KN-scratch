module

public import Definitions.MTT.Def_MTT_Arithmetic

import Definitions.MTT.Def_MTT_Cohomology_Integration
import Theorems.MTT.Thm_MTT_Cohomology_period_cocycle_injective

section privateSection

noncomputable section
open scoped BigOperators
open MTT.Cohomology

namespace P2MPV

variable {N k : ℕ}

/-- A form all of whose vertical periods vanish has vanishing period polynomial. -/
theorem prim_eq_zero (hk : 2 ≤ k) (F : CuspForm (MTT.GammaOne N) (k : ℤ))
    (hF : ∀ j : ℕ, j ≤ k - 2 → ∀ r : ℚ, MTT.modularIntegral F (Polynomial.X ^ j) r = 0)
    (x : Cusp) : cuspPrimitive F x = 0 := by
  induction x using OnePoint.rec with
  | infty => rfl
  | coe r =>
      show cuspPeriodPolynomial F r = 0
      rw [cuspPeriodPolynomial]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hjle : j ≤ k - 2 := by
        have := Finset.mem_range.mp hj
        omega
      rw [hF j hjle r, mul_zero]
      simp

theorem modularIntegral_zero (j : ℕ) (r : ℚ) :
    MTT.modularIntegral ((0 : CuspForm (MTT.GammaOne N) (k : ℤ)) : UpperHalfPlane → ℂ)
      (Polynomial.X ^ j) r = 0 := by
  unfold MTT.modularIntegral
  simp

end P2MPV

open P2MPV in
theorem solution {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (f : CuspForm (MTT.GammaOne N) (k : ℤ))
    (h : ∀ j : ℕ, j ≤ k - 2 → ∀ r : ℚ,
      MTT.modularIntegral f (Polynomial.X ^ j) r = 0) :
    f = 0 := by
  have hf := prim_eq_zero hk f h
  have h0 := prim_eq_zero hk (0 : CuspForm (MTT.GammaOne N) (k : ℤ))
    (fun j _ r => modularIntegral_zero j r)
  refine (MTT.Cohomology.period_cocycle_injective hN hk f 0 0 (Submodule.zero_mem _)
    (fun γ => ?_)).1
  rw [hf, h0, map_zero, map_zero, add_zero, sub_zero]
end

end privateSection

public section publicSection

noncomputable section
open scoped BigOperators

theorem MTT.period_vanishing
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (f : CuspForm (MTT.GammaOne N) (k : ℤ))
    (h : ∀ j : ℕ, j ≤ k - 2 → ∀ r : ℚ,
      MTT.modularIntegral f (Polynomial.X ^ j) r = 0) :
    f = 0 := _root_.solution hN hk f h
end

end publicSection
