module

public import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.QExpansion

import Theorems.KN.Thm_HorizontalPadicL_elliptic_curve_nonvanishing_conditional
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

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


end PalomarChallenge

end publicSection

section privateSection

noncomputable section

open scoped BigOperators Real
open Complex MeasureTheory
open UpperHalfPlane (qExpansion)

namespace PalomarChallenge

lemma character_map_bijective (ι : MTT.Qbar →+* ℂ) (m : ℕ+) :
    Function.Bijective (fun χ : DirichletCharacter MTT.Qbar m => χ.ringHomComp ι) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨MulChar.injective_ringHomComp ι.injective, ?_⟩
  rw [MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity,
    MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity]

def characterEquiv (ι : MTT.Qbar →+* ℂ) :
    HorizontalPadicL.DirichletCharacterWithLevel ≃ CharacterWithModulus :=
  Equiv.sigmaCongrRight fun m => Equiv.ofBijective
    (fun χ : DirichletCharacter MTT.Qbar m => χ.ringHomComp ι)
    (character_map_bijective ι m)

lemma character_map_conductor (ι : MTT.Qbar →+* ℂ) (m : ℕ) [NeZero m]
    (χ : DirichletCharacter MTT.Qbar m) :
    DirichletCharacter.conductor (χ.ringHomComp ι) = χ.conductor := by
  have hker : (χ.ringHomComp ι).toUnitHom.ker = χ.toUnitHom.ker := by
    ext a
    simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom,
      MulChar.ringHomComp_apply]
    simpa only [map_one, Units.val_one] using ι.injective.eq_iff (a := χ a) (b := 1)
  unfold DirichletCharacter.conductor
  apply congrArg sInf
  ext d
  change DirichletCharacter.FactorsThrough (χ.ringHomComp ι) d ↔ χ.FactorsThrough d
  by_cases hd : d ∣ (m : ℕ)
  · rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd,
      DirichletCharacter.factorsThrough_iff_ker_unitsMap hd, hker]
  · exact ⟨fun h => (hd h.dvd).elim, fun h => (hd h.dvd).elim⟩

lemma character_map_order (ι : MTT.Qbar →+* ℂ) (m : ℕ)
    (χ : DirichletCharacter MTT.Qbar m) :
    orderOf (χ.ringHomComp ι) = orderOf χ :=
  orderOf_injective (MulChar.ringHomCompHom ι)
    (MulChar.injective_ringHomComp ι.injective) χ

lemma centralValue_eq (ι : MTT.Qbar →+* ℂ) (f : UpperHalfPlane → ℂ)
    (m : ℕ) (hm : 0 < m) (χ : DirichletCharacter MTT.Qbar m) :
    twistedCentralValue f ⟨m, hm⟩ (χ.ringHomComp ι) =
      @MTT.criticalLValue ι f m ⟨Nat.ne_of_gt hm⟩ χ 0 := by
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  simp only [twistedCentralValue, MTT.criticalLValue, zero_add, pow_one,
    Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, mul_one]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht' : 0 < (I * (t : ℂ)).im := by simpa using ht
  simp [MTT.inverseTwist, MTT.gaussSum,
    UpperHalfPlane.ofComplex_apply_of_im_pos ht']
  rfl

lemma form_eq_of_coeff_eq {N M : ℕ} (hN : 0 < N) (hNM : N = M)
    (f : WeightTwoCuspForm N) (g : WeightTwoCuspForm M)
    (hcoeff : ∀ n : ℕ, (qExpansion 1 f).coeff n = (qExpansion 1 g).coeff n) :
    (f : UpperHalfPlane → ℂ) = g := by
  subst M
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have hfg : (f : ModularForm (CongruenceSubgroup.Gamma0 N) 2) = g := by
    apply ModularForm.qExpansion_injective (h := 1) one_pos (by
      simp [CongruenceSubgroup.strictPeriods_Gamma0])
    exact PowerSeries.ext hcoeff
  exact congrArg (fun g : ModularForm (CongruenceSubgroup.Gamma0 N) 2 =>
    (g : UpperHalfPlane → ℂ)) hfg

end PalomarChallenge

end

end privateSection

public section publicSection

open scoped BigOperators Real
open Complex MeasureTheory
open UpperHalfPlane (qExpansion)

namespace PalomarChallenge

/-- Conditional quantitative nonvanishing for exact-order twists of a modular elliptic curve.
The form is supplied explicitly; coefficient matching and minimality express precisely the
project's modularity and least-level requirements. -/
theorem elliptic_curve_nonvanishing_of_quadratic_seed
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    -- Next lines say: `f` is a modular form whose q-expansion coefficients exactly match the
    -- L-series of `E`, and its level `N` is minimal among such forms.
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
            χ.2.IsPrimitive ∧ orderOf χ.2 = d ∧ (χ.2.conductor : ℝ) ≤ X ∧
            Nat.Coprime N χ.1.1 ∧
            twistedCentralValue f χ.1 χ.2 ≠ 0} := by
  classical
  have hmod : HorizontalPadicL.IsModular E :=
    ⟨N, ⟨{ level_pos := N.2, form := f, coeff_eq := hcoeff }⟩⟩
  have hlevel : (N : ℕ) = HorizontalPadicL.modularConductor E hmod := by
    apply Nat.le_antisymm
    · by_contra h
      exact hminimal
        ⟨HorizontalPadicL.modularConductor E hmod,
          HorizontalPadicL.modularConductor_pos E hmod⟩
        (Nat.lt_of_not_ge h)
        ⟨(HorizontalPadicL.modularFormAtConductor E hmod).form,
          (HorizontalPadicL.modularFormAtConductor E hmod).coeff_eq⟩
    · exact Nat.find_min' hmod ⟨{ level_pos := N.2, form := f, coeff_eq := hcoeff }⟩
  have hform : (f : UpperHalfPlane → ℂ) =
      (HorizontalPadicL.modularFormAtConductor E hmod).form :=
    form_eq_of_coeff_eq N.2 hlevel f _ (fun n =>
      (hcoeff n).symm.trans
        ((HorizontalPadicL.modularFormAtConductor E hmod).coeff_eq n))
  let ι : MTT.Qbar →+* ℂ :=
    (IsAlgClosed.lift (R := ℚ) (S := MTT.Qbar) (M := ℂ)).toRingHom
  let e := characterEquiv ι
  have hseed' : HorizontalPadicL.HasQuadraticTwistSeed
      (HorizontalPadicL.attachedEigenform ι E hmod) d := by
    obtain ⟨η, hprim, horder, hcop, hvalue⟩ := hseed
    let η₀ := e.symm η
    let : NeZero η₀.1.1 := ⟨Nat.ne_of_gt η₀.1.2⟩
    have hη : e η₀ = η := e.apply_symm_apply η
    have hprim₀ : η₀.2.IsPrimitive := by
      have hp : (e η₀).2.IsPrimitive := hη ▸ hprim
      change DirichletCharacter.conductor (η₀.2.ringHomComp ι) = η₀.1.1 at hp
      rwa [character_map_conductor] at hp
    have horder₀ : orderOf η₀.2 = 2 := by
      have ho : orderOf (e η₀).2 = 2 := hη ▸ horder
      change orderOf (η₀.2.ringHomComp ι) = 2 at ho
      rwa [character_map_order] at ho
    have hcop₀ : Nat.Coprime (HorizontalPadicL.modularConductor E hmod * d)
        η₀.2.conductor := by
      have hc : Nat.Coprime (N * d) (e η₀).2.conductor := hη ▸ hcop
      change Nat.Coprime (N * d) (DirichletCharacter.conductor (η₀.2.ringHomComp ι)) at hc
      rwa [character_map_conductor, hlevel] at hc
    refine ⟨η₀, hprim₀, horder₀, hcop₀, ?_⟩
    have hv : twistedCentralValue f (e η₀).1 (e η₀).2 ≠ 0 := hη ▸ hvalue
    change twistedCentralValue f ⟨η₀.1.1, η₀.1.2⟩ (η₀.2.ringHomComp ι) ≠ 0 at hv
    rw [centralValue_eq, hform] at hv
    exact hv
  obtain ⟨α, hα, c, X₀, hc, _, hbound⟩ :=
    HorizontalPadicL.elliptic_curve_nonvanishing_of_quadratic_seed
      ι E d hmod hcase hseed'
  refine ⟨α, c, X₀, hα, hc, ?_⟩
  intro X hX
  have hcount : HorizontalPadicL.nonvanishingCount ι E hmod d X =
      Set.ncard {χ : CharacterWithModulus |
        χ.2.IsPrimitive ∧ orderOf χ.2 = d ∧ (χ.2.conductor : ℝ) ≤ X ∧
        Nat.Coprime N χ.1.1 ∧ twistedCentralValue f χ.1 χ.2 ≠ 0} := by
    unfold HorizontalPadicL.nonvanishingCount
    rw [← Set.ncard_image_of_injective _ e.injective]
    congr 1
    ext χ
    rw [Set.mem_image]
    constructor
    · rintro ⟨χ₀, hχ₀, rfl⟩
      let : NeZero χ₀.1.1 := ⟨Nat.ne_of_gt χ₀.1.2⟩
      change χ₀.2.IsPrimitive ∧ orderOf χ₀.2 = d ∧
        (χ₀.2.conductor : ℝ) ≤ X ∧
        Nat.Coprime (HorizontalPadicL.modularConductor E hmod) χ₀.1.1 ∧
        @MTT.criticalLValue ι (HorizontalPadicL.modularFormAtConductor E hmod).form
          χ₀.1.1 ⟨Nat.ne_of_gt χ₀.1.2⟩ χ₀.2 0 ≠ 0 at hχ₀
      change DirichletCharacter.IsPrimitive (χ₀.2.ringHomComp ι) ∧
        orderOf (χ₀.2.ringHomComp ι) = d ∧
        (DirichletCharacter.conductor (χ₀.2.ringHomComp ι) : ℝ) ≤ X ∧
        Nat.Coprime N χ₀.1.1 ∧
        twistedCentralValue f ⟨χ₀.1.1, χ₀.1.2⟩ (χ₀.2.ringHomComp ι) ≠ 0
      simpa only [DirichletCharacter.IsPrimitive, character_map_conductor,
        character_map_order, centralValue_eq, hform, hlevel] using hχ₀
    · intro hχ
      let : NeZero (e.symm χ).1.1 := ⟨Nat.ne_of_gt (e.symm χ).1.2⟩
      refine ⟨e.symm χ, ?_, e.apply_symm_apply χ⟩
      have hm : e (e.symm χ) = χ := e.apply_symm_apply χ
      rw [← hm] at hχ
      change DirichletCharacter.IsPrimitive ((e.symm χ).2.ringHomComp ι) ∧
        orderOf ((e.symm χ).2.ringHomComp ι) = d ∧
        (DirichletCharacter.conductor ((e.symm χ).2.ringHomComp ι) : ℝ) ≤ X ∧
        Nat.Coprime N (e.symm χ).1.1 ∧
        twistedCentralValue f ⟨(e.symm χ).1.1, (e.symm χ).1.2⟩
          ((e.symm χ).2.ringHomComp ι) ≠ 0 at hχ
      simpa only [Set.mem_ofPred_eq, DirichletCharacter.IsPrimitive, character_map_conductor,
        character_map_order, centralValue_eq, hform, hlevel] using hχ
  simpa only [hcount] using hbound X hX

end PalomarChallenge

end publicSection
