import Definitions.MTT.Def_MTT_PeriodPairing
import Mathlib.NumberTheory.ModularForms.Bounds

noncomputable section
open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Modular ComplexConjugate
open MTT.Cohomology

theorem MTT.Cohomology.periodDensity_integrableOn_tile {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (f q : CuspForm (MTT.GammaOne N) (k : ℤ)) (σ : SL(2, ℤ))
    (D : ℂ → ℂ)
    (hD : ∀ z : ℍ, D z = periodContraction (k - 2)
      (f z • periodPower (k - 2) z)
      (conj (q z) • periodPower (k - 2) (conj (z : ℂ)))) :
    IntegrableOn D ((fun z : ℍ => ((σ • z : ℍ) : ℂ)) '' ModularGroup.fd) := by sorry
