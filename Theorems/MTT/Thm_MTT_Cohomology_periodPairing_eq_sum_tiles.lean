import Definitions.MTT.Def_MTT_PeriodPairing
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.GroupTheory.Complement

noncomputable section
open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Modular ComplexConjugate
open MTT.Cohomology

theorem MTT.Cohomology.periodPairing_eq_sum_tiles {N k : ℕ} (hk : 2 ≤ k)
    (f q : CuspForm (MTT.GammaOne N) (k : ℤ))
    (R : Finset SL(2, ℤ))
    (hR : Subgroup.IsComplement (CongruenceSubgroup.Gamma1 N : Set SL(2, ℤ))
      (R : Set SL(2, ℤ)))
    (D : ℂ → ℂ)
    (hD : ∀ z : ℍ, D z = periodContraction (k - 2)
      (f z • periodPower (k - 2) z)
      (conj (q z) • periodPower (k - 2) (conj (z : ℂ)))) :
    periodPairing N (k - 2) f q =
      ∑ σ ∈ R, ∫ z in (fun τ : ℍ => ((σ • τ : ℍ) : ℂ)) '' ModularGroup.fd,
        D z := by sorry
