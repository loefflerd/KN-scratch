import Definitions.MTT.Def_MTT_Cohomology
import Mathlib.RingTheory.Flat.Basic
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.evaluation_lattice
    {N n : ℕ} (hZ : Module.Finite ℤ (Hc N n ℤ))
    (hQ : BaseChange N n MTT.Qbar) (ψ : Bool → Hc N n MTT.Qbar) :
    (Submodule.span ℤ {v : MTT.Qbar | ∃ s j r, j ≤ n ∧
      v = evaluation j r (ψ s) / (n.choose j : MTT.Qbar)}).FG := by sorry
