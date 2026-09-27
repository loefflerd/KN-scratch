import Definitions.MTT.Def_MTT_Cohomology

set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

/-- A single nonzero finitely generated period lattice can be chosen which is
simultaneously stable under every prime Hecke eigenscalar of an eigenform. -/
theorem MTT.Cohomology.eigenform_uniform_hecke_stable_period_lattice
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) :
    ∃ (ψ : Bool → Hc N (k - 2) MTT.Qbar),
      (∀ s, Packet f.epsilon f.coeff s (ψ s)) ∧
      let L : Submodule ℤ MTT.Qbar :=
        Submodule.span ℤ {v : MTT.Qbar | ∃ s j r, j ≤ k - 2 ∧
          v = evaluation j r (ψ s) / ((k - 2).choose j : MTT.Qbar)}
      L ≠ ⊥ ∧ L.FG ∧ ∀ l : ℕ, l.Prime → ∀ x ∈ L,
        f.coeff l * x ∈ L := by
  sorry
