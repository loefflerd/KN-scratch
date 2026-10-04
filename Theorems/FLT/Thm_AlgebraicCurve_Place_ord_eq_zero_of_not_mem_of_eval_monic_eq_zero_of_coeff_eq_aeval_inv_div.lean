import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial
theorem AlgebraicCurve.Place.ord_eq_zero_of_not_mem_of_eval_monic_eq_zero_of_coeff_eq_aeval_inv_div
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : AlgebraicCurve.Place K F) {j : F} (hj : j ∉ v.toValuationSubring)
    {P Q : F[X]} (hP : P.Monic) (hQ : Q.Monic)
    (hPc : ∀ i, ∃ p q : K[X], q.coeff 0 ≠ 0 ∧ P.coeff i = aeval j⁻¹ p / aeval j⁻¹ q)
    (hQc : ∀ i, ∃ p q : K[X], q.coeff 0 ≠ 0 ∧ Q.coeff i = aeval j⁻¹ p / aeval j⁻¹ q)
    {x : F} (hx : P.eval x = 0) (hx' : Q.eval x⁻¹ = 0) :
    v.ord x = 0 := by sorry
