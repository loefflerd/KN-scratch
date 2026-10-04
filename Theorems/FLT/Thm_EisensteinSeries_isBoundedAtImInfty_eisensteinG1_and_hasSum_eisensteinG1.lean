import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

import Definitions.FLT.Def_EisensteinSeries_WeierstrassZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Real
theorem EisensteinSeries.isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1 (N : ℕ) [NeZero N] :
    (∀ v : Fin 2 → ℤ, (¬ ∀ i, (N : ℤ) ∣ v i) →
        UpperHalfPlane.IsBoundedAtImInfty (EisensteinSeries.eisensteinG1 N v)) ∧
    (∀ (b : ℤ), ¬ (N : ℤ) ∣ b → ∀ τ : UpperHalfPlane,
        HasSum (fun n : ℕ => (if n = 0 then π / N * Complex.cot (π * b / N) else
            -(2 * π * Complex.I) / N * ∑ k ∈ n.divisors,
              (Complex.exp (2 * π * Complex.I * b * k / N) -
                Complex.exp (-(2 * π * Complex.I * b * k / N)))) *
            Complex.exp (2 * π * Complex.I * τ) ^ n)
          (EisensteinSeries.eisensteinG1 N ![0, b] τ)) := by sorry
