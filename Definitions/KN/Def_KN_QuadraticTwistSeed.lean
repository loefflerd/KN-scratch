/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Definitions.KN.Def_KN_HorizontalPadicLAux

/-!
# A nonvanishing quadratic-twist seed

The seed hypothesis used in conditional Kriz–Nordentoft nonvanishing results.
-/

@[expose] public noncomputable section publicSection

/-- A primitive quadratic twist with nonzero central critical value, avoiding
both the modular level and the specified conductor factor. No parity is imposed. -/
def HorizontalPadicL.HasQuadraticTwistSeed
    {N k : ℕ} {ι : MTT.Qbar →+* ℂ} (f : MTT.Eigenform N k ι) (d : ℕ) : Prop :=
    ∃ η : HorizontalPadicL.DirichletCharacterWithLevel,
      η.2.IsPrimitive ∧
      orderOf η.2 = 2 ∧
      Nat.Coprime (N * d) η.2.conductor ∧
      @MTT.criticalLValue ι f.form
        η.1.1 ⟨Nat.ne_of_gt η.1.2⟩ η.2 (k / 2 - 1) ≠ 0

end publicSection
