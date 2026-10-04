import Definitions.MTT.Def_MTT_Cohomology
import Mathlib.RingTheory.Flat.Basic
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.integral_class_character_law_infty
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (φ : Hc N (k-2) ℂ) (hφ : IntegralClass f.form φ)
    (γ : CongruenceSubgroup.Gamma0 N) (r : ℚ) :
    φ.val (cuspAct γ.val OnePoint.infty, cuspAct γ.val ((r : ℚ) : Cusp))
      = ι (f.epsilon (γ.val 1 1 : ZMod N)) •
          act γ.val.val (φ.val (OnePoint.infty, ((r : ℚ) : Cusp))) := by sorry
