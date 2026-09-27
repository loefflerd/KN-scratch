import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Geometry.Manifold.Notation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Complex Real UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm
theorem WLight.exists_analyticOnNhd_div_of_monicRel {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {U : Set 𝕜} (hU : IsOpen U) (hUc : IsPreconnected U)
    {F G : 𝕜 → 𝕜} {c : ℕ → 𝕜 → 𝕜} {n : ℕ}
    (hF : AnalyticOnNhd 𝕜 F U) (hG : AnalyticOnNhd 𝕜 G U) (hG0 : ∃ z ∈ U, G z ≠ 0)
    (hc : ∀ k < n, AnalyticOnNhd 𝕜 (c k) U)
    (hrel : Set.EqOn (F ^ n + ∑ k ∈ Finset.range n, c k * G ^ (n - k) * F ^ k) 0 U) :
    ∃ H : 𝕜 → 𝕜, AnalyticOnNhd 𝕜 H U ∧ Set.EqOn F (G * H) U := by sorry
