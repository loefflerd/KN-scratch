module

public import Theorems.KN.Thm_HorizontalPadicL_elliptic_curve_nonvanishing_conditional

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Set.Card

/-!+# Infinitely many nonvanishing twists of a modular elliptic curve

The conditional quantitative nonvanishing theorem implies infinitude of primitive exact-order
characters with conductor coprime to the modular conductor and nonzero twisted critical value.
The quadratic-seed hypothesis and the restriction on the order are unchanged.
-/

section privateSection

open Filter
open scoped Topology

namespace HorizontalPadicL

private lemma logPowerLowerBound_not_bounded {count : ℝ → ℕ} {α : ℝ}
    (h : HasLogPowerLowerBound count α) (M : ℕ) (hM : ∀ X, count X ≤ M) : False := by
  obtain ⟨c, X₀, hc, hX₀, hb⟩ := h
  have hMpos : 0 < (M : ℝ) + 1 := by positivity
  have hsmall : (fun X : ℝ => Real.log X ^ (1 - α)) =o[atTop] (fun X => X) := by
    simpa only [Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (1 - α) (s := 1) zero_lt_one)
  obtain ⟨Y, hY⟩ := eventually_atTop.1 (hsmall.bound (div_pos hc hMpos))
  let X := max X₀ (max Y 2)
  have hXX₀ : X₀ ≤ X := le_max_left _ _
  have hXY : Y ≤ X := (le_max_left Y 2).trans (le_max_right _ _)
  have hX2 : (2 : ℝ) ≤ X := (le_max_right Y 2).trans (le_max_right _ _)
  have hXpos : 0 < X := by linarith
  have hden : 0 < Real.log X ^ (1 - α) :=
    Real.rpow_pos_of_pos (Real.log_pos (by linarith)) _
  have hnorm := hY X hXY
  simp only [Real.norm_eq_abs, abs_of_nonneg hden.le, abs_of_nonneg hXpos.le] at hnorm
  have hupper : c * X ≤ (M : ℝ) * Real.log X ^ (1 - α) := by
    apply (div_le_iff₀ hden).mp
    exact (hb X hXX₀).trans (by exact_mod_cast hM X)
  have hlower : Real.log X ^ (1 - α) * ((M : ℝ) + 1) ≤ c * X := by
    apply (le_div_iff₀ hMpos).mp
    calc
      Real.log X ^ (1 - α) ≤ c / ((M : ℝ) + 1) * X := hnorm
      _ = c * X / ((M : ℝ) + 1) := by ring
  nlinarith

end HorizontalPadicL

end privateSection

public section publicSection

namespace HorizontalPadicL

/-- Under the quadratic-seed hypothesis, infinitely many primitive exact-order `d` twists,
coprime to the modular conductor, have nonzero critical value. -/
theorem elliptic_curve_infinitely_many_nonvanishing_twists_of_quadratic_seed
    (ι : MTT.Qbar →+* ℂ) (E : WeierstrassCurve ℚ) [E.IsElliptic] (d : ℕ)
    (hmod : IsModular E) (hcase1 : d % 4 = 2 ∧ 6 ≤ d)
    (hSeed : HasQuadraticTwistSeed (attachedEigenform ι E hmod) d) :
    Set.Infinite {χ : DirichletCharacterWithLevel |
      χ.2.IsPrimitive ∧ orderOf χ.2 = d ∧
      Nat.Coprime (modularConductor E hmod) χ.1.1 ∧
      @MTT.criticalLValue ι (modularFormAtConductor E hmod).form
        χ.1.1 ⟨Nat.ne_of_gt χ.1.2⟩ χ.2 0 ≠ 0} := by
  classical
  intro hfinite
  obtain ⟨α, _, hbound⟩ :=
    elliptic_curve_nonvanishing_of_quadratic_seed ι E d hmod hcase1 hSeed
  apply logPowerLowerBound_not_bounded hbound _
  intro X
  unfold nonvanishingCount
  apply Set.ncard_le_ncard _ hfinite
  intro χ hχ
  exact ⟨hχ.1, hχ.2.1, hχ.2.2.2⟩

end HorizontalPadicL

end publicSection
