import Definitions.MTT.Def_MTT_Cohomology
import Mathlib.RingTheory.Flat.Basic
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.signed_packet_multiplicity_one
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (s : Bool) (φ ψ : Hc N (k-2) ℂ)
    (hφ : Packet (fun d => ι (f.epsilon d)) (fun l => ι (f.coeff l)) s φ)
    (hψ : Packet (fun d => ι (f.epsilon d)) (fun l => ι (f.coeff l)) s ψ) :
    ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ a • φ + b • ψ = 0 := by sorry
