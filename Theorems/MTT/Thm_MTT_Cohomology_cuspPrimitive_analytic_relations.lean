import Definitions.MTT.Def_MTT_Cohomology_Integration
import Mathlib.RingTheory.Flat.Basic
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology
theorem MTT.Cohomology.cuspPrimitive_analytic_relations
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) :
    (∀ (f : CuspForm (MTT.GammaOne N) (k : ℤ))
        (γ : CongruenceSubgroup.Gamma1 N) (x : Cusp),
      cuspPrimitive f (cuspAct γ.val x) =
        act γ.val.val (cuspPrimitive f x) +
          cuspPrimitive f (cuspAct γ.val OnePoint.infty)) ∧
    (∀ (f g : CuspForm (MTT.GammaOne N) (k : ℤ)) (x : Cusp),
      cuspPrimitive (f + g) x = cuspPrimitive f x + cuspPrimitive g x) ∧
    (∀ (a : ℂ) (f : CuspForm (MTT.GammaOne N) (k : ℤ)) (x : Cusp),
      cuspPrimitive (a • f) x = a • cuspPrimitive f x) := by sorry
