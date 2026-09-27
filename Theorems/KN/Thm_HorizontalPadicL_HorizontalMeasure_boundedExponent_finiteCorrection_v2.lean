import Definitions.KN.Def_KN_PrimePowerPropagationV2

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HorizontalPadicL

/-- Nonvanishing-only maximal-order Fourier lemma for integral Cp-valued
horizontal measures. First push each coordinate down to p^m. The intended proof
uses the maximal-order orthogonality argument of Kriz--Nordentoft Proposition
2.10 and Section 2.3.3. Theorem 2.8 alone does not suffice when m > 1.
Unlike the valuation-equality version of Theorem 2.13, this statement asks only
for nonvanishing; its proof must justify this integral-Cp generality explicitly.
Source: https://arxiv.org/pdf/2310.20678 . -/
theorem HorizontalMeasure.boundedExponent_finiteCorrection_v2
    {p : ℕ} [Fact p.Prime] {e : ℕ → ℕ} {R : Subring ℂ_[p]}
    (μ : HorizontalMeasure R p e)
    (hintegral : ∀ x : R, (x : ℂ_[p]) ∈ 𝓞_ℂ_[p])
    (m : ℕ) (hm : 0 < m) (he : ∀ n, m ≤ e n)
    (htriv : μ.eval (trivialHorizontalCharacterV2 p e) ≠ 0) :
    ∃ A : Finset ℕ, μ.HasFiniteCorrection m A := by
  sorry

end HorizontalPadicL
