import Definitions.FLT.Def_ModularCurve_PrimCosetReps
import Definitions.FLT.Def_PeriodPair_Uniformization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
theorem PeriodPair.exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic
    {N : ℕ} [NeZero N] (L L' : PeriodPair)
    (hsub : (L'.lattice : Set ℂ) ⊆ L.lattice) (hidx : PeriodPair.sublatticeIndex L L' = N)
    (hcyc : IsAddCyclic (PeriodPair.sublatticeQuotient L L')) :
    ∃ (a b d : ℕ) (τ σ : ℍ), (a, b, d) ∈ ModularCurve.primCosetReps N ∧
      (σ : ℂ) = ((a : ℂ) * τ + b) / d ∧
      L.jLattice = (PeriodPair.ofTau τ).jLattice ∧ L'.jLattice = (PeriodPair.ofTau σ).jLattice := by sorry
