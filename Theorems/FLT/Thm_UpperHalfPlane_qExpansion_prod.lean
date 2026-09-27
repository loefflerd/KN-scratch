import Mathlib.NumberTheory.ModularForms.QExpansion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped Manifold
theorem UpperHalfPlane.qExpansion_prod {h : ℝ} {ι : Type*} (s : Finset ι) {F : ι → ℍ → ℂ} (hF : ∀ i ∈ s, AnalyticAt ℂ (cuspFunction h (F i)) 0) : qExpansion h (∏ i ∈ s, F i) = ∏ i ∈ s, qExpansion h (F i) := by sorry
