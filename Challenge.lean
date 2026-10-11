module

public import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# Non-vanishing of finite-order twists of an elliptic curve

This is a formalized statement of the first case of Theorem 1.1 in the paper

Daniel Kriz and Asbjørn Nordentoft, _Horizontal p-adic L-functions_, https://arxiv.org/abs/2310.20678

We add two extra hypotheses not present in the source, corresponding to major
theorems which are beyond the scope of this project to formalize: firstly, modularity of the
elliptic curve; secondly, the existence of a single quadratic twist with non-vanishing
L-value.

The modularity hypothesis supplies a weight-two cusp form whose q-expansion is exactly the
arithmetic L-series of the curve. The level is required to be the least positive level admitting
such a form. This is the project's working definition of "modular conductor".

The remaining conditional input is a single primitive quadratic twist with nonzero central
value and conductor coprime to `N * d`. No parity restriction is placed on this seed.

The conclusion counts primitive characters of exact order `d`, with conductor at most `X`
and coprime to `N`, having nonzero central value. The inverse-character convention in the
Mellin integral is exactly the convention used by the existing development.
-/

@[expose] public noncomputable section publicSection

open scoped BigOperators Real
open Complex MeasureTheory
open UpperHalfPlane (qExpansion)

namespace PalomarChallenge

/-- A weight-two cusp form on `Γ₀(N)`, with positivity providing the required instance. -/
abbrev WeightTwoCuspForm (N : ℕ) := CuspForm (CongruenceSubgroup.Gamma0 N) 2

/-- Condition that a given elliptic curve and modular form have exactly matching L-series.
Takes a specific choice of Weierstrass model over `ℚ` as input, but is independent of the
choice of model, because the definition of the elliptic curve L-series uses a local minimal
model at each place. -/
abbrev IsModularWith (E : WeierstrassCurve ℚ) (N : ℕ+) (f : WeightTwoCuspForm N) : Prop :=
  ∀ n : ℕ, E.LFunction n = (qExpansion 1 f).coeff n

/-- A complex Dirichlet character together with its positive modulus.
For a primitive character this modulus is its conductor. -/
abbrev CharacterWithModulus := Σ m : ℕ+, DirichletCharacter ℂ m.1

/-- The central value of the inverse-character twist `L(E, χ⁻¹, 1)`, defined by a Mellin
integral. The denominator is the Gauss sum of `χ` with the positive exponential. The
normalization is `2π ∫₀^∞ f_{χ⁻¹}(it) dt`, the weight-two, `j = 0` specialization used in KN. -/
def twistedCentralValue (f : UpperHalfPlane → ℂ)
    (m : ℕ+) (χ : DirichletCharacter ℂ m) : ℂ :=
  (2 * π : ℂ) * ∫ t in Set.Ioi (0 : ℝ),
    (∑ a : ZMod m, χ a * exp (2 * π * I * a.val / m))⁻¹ *
    ∑ a : ZMod m, χ a * f (UpperHalfPlane.ofComplex (I * t + a.val / m))

/-- Conditional quantitative nonvanishing for exact-order twists of a modular elliptic curve.
The form is supplied explicitly; coefficient matching and minimality express precisely the
project's modularity and least-level requirements. -/
theorem elliptic_curve_nonvanishing_of_quadratic_seed
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    -- Next lines say: `f` is a modular form of level `N` whose q-expansion coefficients exactly
    -- match the L-series of `E`; and `N` is minimal for the existence of such a form.
    (N : ℕ+) (f : WeightTwoCuspForm N) (hcoeff : IsModularWith E N f)
    (hminimal : ∀ M < N, ¬ ∃ g, IsModularWith E M g)
    (d : ℕ) (hcase : d % 4 = 2 ∧ 6 ≤ d)
    -- Next line is *assuming* the existence of a non-vanishing quadratic twist of conductor
    -- coprime to `N * d` (which is actually known unconditionally by Friedberg-Hoffstein, but
    -- that is not formalized in the project)
    (hseed : ∃ η : CharacterWithModulus, η.2.IsPrimitive ∧ orderOf η.2 = 2 ∧
      Nat.Coprime (N * d) η.2.conductor ∧ twistedCentralValue f η.1 η.2 ≠ 0) :
    ∃ α c X₀ : ℝ, 0 < α ∧ 0 < c ∧ ∀ X : ℝ, X₀ ≤ X →
        c * X / X.log ^ (1 - α) ≤
          Set.ncard {χ : CharacterWithModulus |
            χ.2.IsPrimitive ∧ orderOf χ.2 = d ∧ χ.2.conductor ≤ X ∧
            Nat.Coprime N χ.1.1 ∧ twistedCentralValue f χ.1 χ.2 ≠ 0} := by
  sorry -- to be supplied by the rest of the files here

end PalomarChallenge

end publicSection
