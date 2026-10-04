module

public import Definitions.KN.Def_KN_PrimePowerPropagationV2

@[expose] public section publicSection

noncomputable section

namespace HorizontalPadicL

/-- Reduce every coordinate of a finite horizontal quotient modulo `p ^ m`. -/
def truncateHorizontalCoordinates {p : ℕ} {e : ℕ → ℕ} (m : ℕ)
    (he : ∀ n, m ≤ e n) (A : Finset ℕ) :
    HorizontalFiniteGroup p e A → HorizontalFiniteGroup p (fun _ ↦ m) A :=
  fun x i ↦ Multiplicative.ofAdd
    (ZMod.castHom (pow_dvd_pow p (he i.1)) (ZMod (p ^ m)) (x i).toAdd)

/-- The finite-level coefficients after reducing every coordinate modulo `p ^ m`.
Coefficients in the same fibre are added in the original coefficient ring. -/
def HorizontalMeasure.truncatedFiniteLevel {R : Type*} [CommRing R]
    {p : ℕ} {e : ℕ → ℕ} (μ : HorizontalMeasure R p e) (m : ℕ)
    (he : ∀ n, m ≤ e n) (A : Finset ℕ) :
    HorizontalGroupRing R p (fun _ ↦ m) A :=
  Finsupp.mapDomain (truncateHorizontalCoordinates m he A) (μ.finiteLevel A)

end HorizontalPadicL

end

end publicSection
