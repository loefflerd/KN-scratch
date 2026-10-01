import Definitions.FLT.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
theorem ZMod.natCard_isAddCyclic_addSubgroup_prod_map_eq_nuThree (n : ℕ) [NeZero n]
    (τ : ZMod n × ZMod n →+ ZMod n × ZMod n) (hτ : ∀ v, τ (τ v) + τ v + v = 0)
    (hns : ∀ p : ℕ, p.Prime → p ∣ n → ∃ v : ZMod n × ZMod n, addOrderOf v = p ∧ ∀ k : ℕ, τ v ≠ k • v) :
    Nat.card {H : AddSubgroup (ZMod n × ZMod n) // IsAddCyclic H ∧ Nat.card H = n ∧ H.map τ = H}
      = nuThree n := by sorry
