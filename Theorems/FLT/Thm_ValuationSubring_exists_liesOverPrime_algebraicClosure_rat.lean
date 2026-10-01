import Definitions.FLT.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ValuationSubring.exists_liesOverPrime_algebraicClosure_rat (p : Nat.Primes) :
    ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (p : ℕ) := by sorry
