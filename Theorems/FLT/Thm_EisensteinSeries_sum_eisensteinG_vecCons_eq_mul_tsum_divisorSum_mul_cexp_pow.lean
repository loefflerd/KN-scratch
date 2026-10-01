import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

import Definitions.FLT.Def_EisensteinSeries_EisensteinG

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Real in
theorem EisensteinSeries.sum_eisensteinG_vecCons_eq_mul_tsum_divisorSum_mul_cexp_pow
    (N : ℕ) [NeZero N] (a : ZMod N) (ha : a ≠ 0) {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (z : UpperHalfPlane) :
    ∑ e : ZMod N, EisensteinSeries.eisensteinG N k ![a, e] z =
      ((-2 * π * Complex.I) ^ k / (Nat.factorial (k - 1) : ℂ)) *
        ∑' n : ℕ, (∑ d ∈ n.divisors,
            ((if ((n / d : ℕ) : ZMod N) = a then (d : ℂ) ^ (k - 1) else 0) +
              (if ((n / d : ℕ) : ZMod N) = -a then (d : ℂ) ^ (k - 1) else 0))) *
          Complex.exp (2 * π * Complex.I * z) ^ n := by sorry
