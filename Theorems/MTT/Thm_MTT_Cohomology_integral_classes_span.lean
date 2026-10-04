import Definitions.MTT.Def_MTT_Cohomology
import Mathlib.RingTheory.Flat.Basic
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.integral_classes_span
    {N n : ℕ} (hN : 0 < N) (R : Type*) [CommRing R] [Module.Flat ℤ R]
    (Φ : Hc N n R) :
    ∃ (m : ℕ) (c : Fin m → R) (φ : Fin m → Hc N n ℤ),
      ∀ D : Cusp × Cusp,
        Φ.val D = ∑ i, c i • MvPolynomial.map (Int.castRingHom R) ((φ i).val D) := by sorry
