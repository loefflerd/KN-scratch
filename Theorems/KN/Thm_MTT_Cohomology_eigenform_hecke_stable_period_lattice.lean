import Definitions.MTT.Def_MTT_Cohomology

noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.eigenform_hecke_stable_period_lattice
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (l : ℕ) (hl : l.Prime) :
    ∃ (ψ : Bool → Hc N (k - 2) MTT.Qbar),
      (∀ s, Packet f.epsilon f.coeff s (ψ s)) ∧
      let L : Submodule ℤ MTT.Qbar :=
        Submodule.span ℤ {v : MTT.Qbar | ∃ s j r, j ≤ k - 2 ∧
          v = evaluation j r (ψ s) / ((k - 2).choose j : MTT.Qbar)}
      L ≠ ⊥ ∧ L.FG ∧ ∀ x ∈ L, f.coeff l * x ∈ L := by
  sorry
