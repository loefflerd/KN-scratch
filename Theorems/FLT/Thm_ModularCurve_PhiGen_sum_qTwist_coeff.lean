import Definitions.FLT.Def_ModularCurve_PhiGen
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.sum_qTwist_coeff {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) (f : LaurentSeries K) (k : ℤ) : (∑ b ∈ Finset.range ℓ, qTwist (ζ ^ b) f).coeff k = if (ℓ : ℤ) ∣ k then (ℓ : K) * f.coeff k else 0 := by sorry
