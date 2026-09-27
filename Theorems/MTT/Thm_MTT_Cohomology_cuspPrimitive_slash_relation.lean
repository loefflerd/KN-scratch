import Definitions.MTT.Def_MTT_Cohomology_Integration
import Mathlib.RingTheory.Flat.Basic
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.cuspPrimitive_slash_relation
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (g g' : CuspForm (MTT.GammaOne N) (k : ℤ)) (γ : CongruenceSubgroup.Gamma0 N)
    (hg' : ∀ z : UpperHalfPlane,
      g ((Matrix.SpecialLinearGroup.mapGL ℝ γ.val) • z) =
        (((γ.val 1 0 : ℤ) : ℂ) * z + ((γ.val 1 1 : ℤ) : ℂ)) ^ k * g' z)
    (x : Cusp) :
    cuspPrimitive g (cuspAct γ.val x) =
      act γ.val.val (cuspPrimitive g' x) + cuspPrimitive g (cuspAct γ.val OnePoint.infty) := by sorry
