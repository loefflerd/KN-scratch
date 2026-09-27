import Definitions.MTT.Def_MTT_Cohomology
import Mathlib.RingTheory.Flat.Basic
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.eigenclass_descent
    {N n : ℕ} (hZ : Module.Finite ℤ (Hc N n ℤ))
    (hQ : BaseChange N n MTT.Qbar) (hC : BaseChange N n ℂ)
    (ι : MTT.Qbar →+* ℂ) (e : DirichletCharacter MTT.Qbar N)
    (a : ℕ → MTT.Qbar) (s : Bool)
    (hdim : ∀ φ ψ : Hc N n ℂ,
      Packet (fun d => ι (e d)) (fun l => ι (a l)) s φ →
      Packet (fun d => ι (e d)) (fun l => ι (a l)) s ψ →
      ∃ u v : ℂ, (u ≠ 0 ∨ v ≠ 0) ∧ u • φ + v • ψ = 0)
    (φ : Hc N n ℂ)
    (hφ : Packet (fun d => ι (e d)) (fun l => ι (a l)) s φ) :
    ∃ ω : ℂ, ω ≠ 0 ∧ ∃ ψ : Hc N n MTT.Qbar, Extends ι ψ (ω⁻¹ • φ) := by sorry
