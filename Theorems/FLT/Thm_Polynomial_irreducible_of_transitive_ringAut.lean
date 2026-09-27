import Mathlib.Algebra.Polynomial.Splits

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem Polynomial.irreducible_of_transitive_ringAut {F L : Type*} [Field F] [Field L] [Algebra F L] (P : Polynomial F) (hP : P.Monic) (hPs : (P.map (algebraMap F L)).Splits) (σ : L ≃+* L) (hσ : ∀ a : F, σ (algebraMap F L a) = algebraMap F L a) (y₀ : L) (r : ℕ → L) (n : ℕ) (hroots : (P.map (algebraMap F L)).roots = y₀ ::ₘ (Multiset.range n).map r) (hnodup : (P.map (algebraMap F L)).roots.Nodup) (hcycle : ∀ i < n, σ (r i) = r ((i + 1) % n)) (hy₀ : y₀ ∉ (algebraMap F L).range) : Irreducible P := by sorry
