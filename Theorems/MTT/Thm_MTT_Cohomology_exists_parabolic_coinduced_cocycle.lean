import Definitions.MTT.Def_MTT_ParabolicCohomology
import Mathlib.RepresentationTheory.Coinduced
set_option autoImplicit false
noncomputable section

theorem MTT.Cohomology.exists_parabolic_coinduced_cocycle {N n : ℕ} (hN : 0 < N)
    (b : MTT.Cohomology.parabolicCocycles N n) :
    ∃ c : groupCohomology.cocycles₁
        (Rep.coind (CongruenceSubgroup.Gamma1 N).subtype (MTT.Cohomology.gammaOneRep N n)),
      (∀ h : CongruenceSubgroup.Gamma1 N, (c h.val).val 1 = b.val h) ∧
      ∀ (x : MTT.Cohomology.Cusp) (g : Matrix.SpecialLinearGroup (Fin 2) ℤ),
        MTT.Cohomology.cuspAct g x = x →
        ∃ P : Rep.coind (CongruenceSubgroup.Gamma1 N).subtype (MTT.Cohomology.gammaOneRep N n),
          c g = (Rep.coind (CongruenceSubgroup.Gamma1 N).subtype
            (MTT.Cohomology.gammaOneRep N n)).ρ g P - P := by sorry
