import Definitions.KN.Def_KN_PrimePowerPropagationV2

noncomputable section
open scoped BigOperators

namespace HorizontalPadicL

/-- Counting exact-order characters supported on a positive-density set of
primes congruent to 1 modulo p^m, after finitely many primes are excluded.
The strict slack in alpha avoids an endpoint asymptotic from mere natural
density. Intended proof: weighted squarefree counting (a weakened form of
Kriz--Nordentoft Lemma 5.7), followed by removing lower-order characters.
Source: https://arxiv.org/pdf/2310.20678 . -/
theorem supportedPrimePowerCharacters_logLowerBound_v2
    (p m : ℕ) [Fact p.Prime] (hm : 0 < m)
    (ℓ : ℕ → ℕ) (hprime : ∀ n, (ℓ n).Prime)
    (hinj : Function.Injective ℓ) (hcong : ∀ n, Nat.ModEq (p ^ m) (ℓ n) 1)
    (δ : ℝ) (hδ : 0 < δ)
    (hdensity : HasPrimeNaturalDensity (Set.range ℓ) δ)
    (A : Finset ℕ) :
    ∃ α : ℝ, 0 < α ∧ α < ((p ^ m - 1 : ℕ) : ℝ) * δ ∧
      HasLogPowerLowerBound
        (characterConductorCount (supportedPrimePowerCharacters ℓ A p m)) α := by
  sorry

end HorizontalPadicL
