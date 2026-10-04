import Definitions.MTT.Def_MTT_Cohomology
import Mathlib.RingTheory.Flat.Basic
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.manin_generation_span
    {N n : ℕ} {R : Type*} [CommRing R] (φ : Hc N n R) (x y : Cusp) :
    φ.val (x, y) ∈ AddSubgroup.closure
      (Set.range fun g : Matrix.SpecialLinearGroup (Fin 2) ℤ =>
        φ.val (cuspAct g ((0 : ℚ) : Cusp), cuspAct g OnePoint.infty)) := by sorry
