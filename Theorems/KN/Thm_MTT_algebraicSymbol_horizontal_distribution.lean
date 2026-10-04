import Definitions.MTT.Def_MTT_Measures

noncomputable section
open scoped BigOperators

open MTT in
/-- The arbitrary-denominator form of the Hecke distribution relation for
algebraic modular symbols.  This is the part of the proof of
`MTT.distribution_relation` before ordinary-root stabilization. -/
theorem MTT.algebraicSymbol_horizontal_distribution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (f : Eigenform N k ι) (P : Periods k ι f.form)
    (s : Bool) (j : ℕ) (hj : j ≤ k - 2)
    (ℓ q : ℕ) (hℓ : ℓ.Prime) (hq : 0 < q) (a : ℤ) :
    (∑ b ∈ Finset.range ℓ,
      algebraicSymbol P s j
        ((a : ℚ) + (b : ℚ) * (q : ℚ)) ((ℓ : ℚ) * (q : ℚ))) =
      f.coeff ℓ * algebraicSymbol P s j (a : ℚ) (q : ℚ) -
        f.epsilon ℓ * (ℓ : Qbar) ^ (k - 2 - j) *
          algebraicSymbol P s j ((ℓ : ℚ) * (a : ℚ)) (q : ℚ) := by
  sorry
