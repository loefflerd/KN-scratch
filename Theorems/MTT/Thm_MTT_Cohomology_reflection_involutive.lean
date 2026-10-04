import Definitions.MTT.Def_MTT_Cohomology
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.reflection_involutive {R : Type*} [CommRing R]
    (φ : (Cusp × Cusp) → Binary R) : reflection (reflection φ) = φ := by sorry
