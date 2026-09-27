import Definitions.FLT.Def_ModularCurve_JqCoeff
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.Relrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ModularCurve.relfinrank_fullC_mul_prime_pow {K : Type*} [Field K] (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (a : ℕ) (hpM : ¬ p ∣ M) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (M * p ^ (a + 1))) (hprev : ∀ b : ℕ, a = b + 1 → IntermediateField.relfinrank (IntermediateField.adjoin K {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ M * p ^ b ∧ x = jqNModC K d'}) (IntermediateField.adjoin K {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ M * p ^ (b + 1) ∧ x = jqNModC K d'}) = if b = 0 then p + 1 else p) (hnm : a = 0 → jqNModC K p ∉ IntermediateField.adjoin K {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ M ∧ x = jqNModC K d'}) : IntermediateField.relfinrank (IntermediateField.adjoin K {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ M * p ^ a ∧ x = jqNModC K d'}) (IntermediateField.adjoin K {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ M * p ^ (a + 1) ∧ x = jqNModC K d'}) = if a = 0 then p + 1 else p := by sorry
