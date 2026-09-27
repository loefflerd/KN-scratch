import Definitions.MTT.Def_MTT_Arithmetic
set_option autoImplicit false
noncomputable section
open scoped BigOperators

theorem MTT.exists_cuspForm_heckePrime_pos
    {N k : ℕ} (hN : 0 < N) (hk : 1 ≤ k) (e : DirichletCharacter ℂ N)
    (g : CuspForm (MTT.GammaOne N) (k : ℤ))
    (hg : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane,
      g ((Matrix.SpecialLinearGroup.mapGL ℝ γ.val) • z) =
        e (γ.val 1 1 : ZMod N) *
          (((γ.val 1 0 : ℤ) : ℂ) * z + ((γ.val 1 1 : ℤ) : ℂ)) ^ k * g z)
    (l : ℕ) (hl : l.Prime) :
    ∃ g' : CuspForm (MTT.GammaOne N) (k : ℤ),
      (∀ z, g' z = MTT.heckePrime k (e (l : ZMod N)) l g z) ∧
      ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane,
        g' ((Matrix.SpecialLinearGroup.mapGL ℝ γ.val) • z) =
          e (γ.val 1 1 : ZMod N) *
            (((γ.val 1 0 : ℤ) : ℂ) * z + ((γ.val 1 1 : ℤ) : ℂ)) ^ k * g' z := by sorry
