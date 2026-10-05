module

public import Definitions.MTT.Def_MTT_PeriodPairing

import Mathlib.GroupTheory.Complement
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

section privateSection

noncomputable section

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
end

end privateSection

public section publicSection

noncomputable section
open scoped MatrixGroups

theorem MTT.Cohomology.gammaOne_has_finset_complement
    {N : ℕ} (hN : 0 < N) :
    ∃ R : Finset (Matrix.SpecialLinearGroup (Fin 2) ℤ),
      Subgroup.IsComplement
        (CongruenceSubgroup.Gamma1 N : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
        (R : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)) := _root_.solution hN
end

end publicSection
