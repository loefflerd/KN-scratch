import Definitions.MTT.Def_MTT_PeriodPairing

noncomputable section
open scoped MatrixGroups

theorem MTT.Cohomology.gammaOne_has_finset_complement
    {N : ℕ} (hN : 0 < N) :
    ∃ R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ),
      Subgroup.IsComplement
        (CongruenceSubgroup.Gamma1 N : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
        (R : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)) := by sorry
