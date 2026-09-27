import Definitions.MTT.Def_MTT_Arithmetic
set_option autoImplicit false
noncomputable section
open scoped BigOperators

theorem MTT.exists_cuspForm_slash_gamma0
    {N k : ℕ} (hN : 0 < N) (g : CuspForm (MTT.GammaOne N) (k : ℤ))
    (γ : CongruenceSubgroup.Gamma0 N) :
    ∃ g' : CuspForm (MTT.GammaOne N) (k : ℤ), ∀ z : UpperHalfPlane,
      g ((Matrix.SpecialLinearGroup.mapGL ℝ γ.val) • z) =
        (((γ.val 1 0 : ℤ) : ℂ) * z + ((γ.val 1 1 : ℤ) : ℂ)) ^ k * g' z := by sorry
