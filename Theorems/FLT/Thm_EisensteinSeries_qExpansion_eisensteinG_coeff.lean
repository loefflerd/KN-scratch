import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.ModularForms.QExpansion

import Definitions.FLT.Def_EisensteinSeries_EisensteinG

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Real Complex
open scoped Nat
theorem EisensteinSeries.qExpansion_eisensteinG_coeff (N : ℕ) [NeZero N] (k : ℕ) (hk : 3 ≤ k)
    (a : Fin 2 → ZMod N) (n : ℕ) :
    (UpperHalfPlane.qExpansion N (EisensteinSeries.eisensteinG N k a)).coeff n =
      if n = 0 then
        (if a 0 = 0 then ∑' d : {d : ℤ // (d : ZMod N) = a 1}, ((d : ℂ) ^ k)⁻¹ else 0)
      else
        (-2 * π * I) ^ k / ((k - 1)! * (N : ℂ) ^ k) *
          ∑ m ∈ n.divisors,
            ((if ((n / m : ℕ) : ZMod N) = a 0 then ZMod.stdAddChar (a 1 * (m : ZMod N)) else 0) +
              (-1) ^ k *
                (if ((n / m : ℕ) : ZMod N) = -a 0 then ZMod.stdAddChar (-(a 1 * (m : ZMod N))) else 0)) *
            (m : ℂ) ^ (k - 1) := by sorry
