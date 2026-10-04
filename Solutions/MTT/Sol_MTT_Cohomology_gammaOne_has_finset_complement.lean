import Definitions.MTT.Def_MTT_PeriodPairing

noncomputable section

open MTT.Cohomology

theorem solution
    {N : ℕ} (hN : 0 < N) :
    ∃ R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ),
      Subgroup.IsComplement
        (CongruenceSubgroup.Gamma1 N : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
        (R : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)) := by
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  obtain ⟨T, hT, -⟩ :=
    (CongruenceSubgroup.Gamma1 N).exists_isComplement_right 1
  have hTfinite : T.Finite := hT.finite_right
  exact ⟨hTfinite.toFinset, by simpa using hT⟩
