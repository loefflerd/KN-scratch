module

public import Definitions.MTT.Def_MTT_Arithmetic
public import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section publicSection

namespace HorizontalPadicL

/-- Quantitative lower-bound notation used in Theorem 1.1. -/
def HasLogPowerLowerBound (count : ℝ → ℕ) (α : ℝ) : Prop :=
  ∃ c X₀ : ℝ, 0 < c ∧ 1 ≤ X₀ ∧
    ∀ X : ℝ, X₀ ≤ X → c * X / (Real.log X) ^ (1 - α) ≤ count X

/-- An algebraic Dirichlet character together with its level. -/
abbrev DirichletCharacterWithLevel :=
  Σ N : {N : ℕ // 0 < N}, DirichletCharacter MTT.Qbar N.1

/-- Weight-two cusp forms for `Γ₀(N)`, with positivity supplied explicitly. -/
abbrev CuspFormAtLevel (N : ℕ) (hN : 0 < N) :=
  let _ : NeZero N := ⟨Nat.ne_of_gt hN⟩
  CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2

/-- A weight-two cusp form of level `N` whose q-expansion coefficients are the
arithmetic L-series coefficients of `E`. -/
structure ModularFormAtLevel (E : WeierstrassCurve ℚ) (N : ℕ) where
  level_pos : 0 < N
  form : CuspFormAtLevel N level_pos
  coeff_eq : ∀ n : ℕ, (E.LFunction n : ℂ) =
    (UpperHalfPlane.qExpansion 1 form).coeff n

/-- A rational elliptic curve is modular if it has an associated weight-two cusp form
at some positive level. -/
def IsModular (E : WeierstrassCurve ℚ) : Prop :=
  ∃ N : ℕ, Nonempty (ModularFormAtLevel E N)

/-- The least level of a modular form associated with `E`. -/
noncomputable def modularConductor (E : WeierstrassCurve ℚ) (hE : IsModular E) : ℕ := by
  classical
  exact Nat.find hE

/-- A chosen modular form associated with `E` at its least level. -/
noncomputable def modularFormAtConductor (E : WeierstrassCurve ℚ) (hE : IsModular E) :
    ModularFormAtLevel E (modularConductor E hE) := by
  classical
  exact Classical.choice (Nat.find_spec hE)

lemma modularConductor_pos (E : WeierstrassCurve ℚ) (hE : IsModular E) :
    0 < modularConductor E hE :=
  (modularFormAtConductor E hE).level_pos

/-- Number of primitive exact-order characters of conductor at most `X`, coprime to
`N(E)`, for which the twisted critical value defined by the MTT Mellin integral is
nonzero. No twisted modular form is constructed or chosen. -/
noncomputable def nonvanishingCount (ι : MTT.Qbar →+* ℂ)
    (E : WeierstrassCurve ℚ) (hE : IsModular E) (d : ℕ) (X : ℝ) : ℕ :=
  let P := modularFormAtConductor E hE
  Set.ncard {χ : DirichletCharacterWithLevel |
    χ.2.IsPrimitive ∧ orderOf χ.2 = d ∧ (χ.2.conductor : ℝ) ≤ X ∧
    Nat.Coprime (modularConductor E hE) χ.1.1 ∧
    @MTT.criticalLValue ι P.form χ.1.1 ⟨Nat.ne_of_gt χ.1.2⟩ χ.2 0 ≠ 0}

end HorizontalPadicL

end publicSection
