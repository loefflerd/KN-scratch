import Definitions.MTT.Def_MTT_Cohomology
import Mathlib.RingTheory.Flat.Basic
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.manin_generation
    {N n : ℕ} {R : Type*} [CommRing R] (φ : Hc N n R)
    (hU : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      φ.val (cuspAct g ((0 : ℚ) : Cusp), cuspAct g OnePoint.infty) = 0) :
    φ = 0 := by sorry
