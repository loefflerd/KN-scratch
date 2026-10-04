import Definitions.MTT.Def_MTT_FullParabolicCohomology
import Definitions.MTT.Def_MTT_ParabolicCohomology
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Tactic
import Mathlib.Tactic.Module

/-! # Coinduction of a restricted representation as functions on left cosets -/

noncomputable section

namespace Rep

variable {K G : Type} [Field K] [Group G] (A : Rep K G) (H : Subgroup G)

def coindCosetCoordinates : coind H.subtype (res H.subtype A) ≃ₗ[K] (G ⧸ H → A) where
  toFun f := Quotient.lift (fun x : G => A.ρ x (f.val x⁻¹)) (by
    intro x y hxy
    have hh : x⁻¹ * y ∈ H := QuotientGroup.leftRel_apply.mp hxy
    let h : H := ⟨x⁻¹ * y, hh⟩
    have hy : y = x * h.val := by simp [h]
    rw [hy, mul_inv_rev]
    have hp := f.property h⁻¹ x⁻¹
    change f.val (h.val⁻¹ * x⁻¹) = A.ρ h.val⁻¹ (f.val x⁻¹) at hp
    rw [hp, ← Module.End.mul_apply, ← map_mul]
    simp only [mul_inv_cancel_right])
  invFun F := ⟨fun x => A.ρ x (F (QuotientGroup.mk x⁻¹)), by
    intro h x
    have hx : (QuotientGroup.mk ((h.val * x)⁻¹) : G ⧸ H) = QuotientGroup.mk x⁻¹ := by
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      simpa only [inv_inv, mul_inv_cancel_right] using h.property
    change A.ρ (h.val * x) (F (QuotientGroup.mk ((h.val * x)⁻¹))) =
      A.ρ h.val (A.ρ x (F (QuotientGroup.mk x⁻¹)))
    rw [hx, map_mul, Module.End.mul_apply]⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    change A.ρ x (A.ρ x⁻¹ (f.val x⁻¹⁻¹)) = f.val x
    rw [inv_inv, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  right_inv F := by
    funext q
    induction q using Quotient.inductionOn with
    | h x =>
        change A.ρ x (A.ρ x⁻¹ (F (QuotientGroup.mk x⁻¹⁻¹))) = F (QuotientGroup.mk x)
        rw [inv_inv, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
  map_add' f g := by
    funext q
    induction q using Quotient.inductionOn with
    | h x => exact map_add _ _ _
  map_smul' a f := by
    funext q
    induction q using Quotient.inductionOn with
    | h x => exact map_smul _ _ _

theorem coindCosetCoordinates_action (g : G) (f : coind H.subtype (res H.subtype A))
    (q : G ⧸ H) :
    coindCosetCoordinates A H ((coind H.subtype (res H.subtype A)).ρ g f) q =
      A.ρ g (coindCosetCoordinates A H f (g⁻¹ • q)) := by
  induction q using Quotient.inductionOn with
  | h x =>
      change A.ρ x (f.val (x⁻¹ * g)) = A.ρ g (A.ρ (g⁻¹ * x) (f.val (g⁻¹ * x)⁻¹))
      rw [mul_inv_rev, inv_inv, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

end Rep

/-! # The global symmetric-power representation underlying the MTT coefficients -/

noncomputable section

open scoped MatrixGroups

namespace MTT.Cohomology

def fullSymRep (n : ℕ) : Rep ℂ SL(2, ℤ) :=
  Rep.of ((symRepresentation ⊤ n ℂ).ρ.comp
    { toFun := fun g => ⟨g, Subgroup.mem_top g⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl })

theorem gammaOneRep_eq_res_fullSymRep (N n : ℕ) :
    gammaOneRep N n = Rep.res (CongruenceSubgroup.Gamma1 N).subtype (fullSymRep n) := rfl

end MTT.Cohomology

/-! # Finite-order fixed dimensions in the full coinduced coefficient module -/

noncomputable section

open scoped MatrixGroups

namespace MTT.Cohomology

abbrev fullCoinduced (N n : ℕ) :=
  Rep.coind (CongruenceSubgroup.Gamma1 N).subtype (gammaOneRep N n)

def fullCoinducedCoordinates (N n : ℕ) :
    fullCoinduced N n ≃ₗ[ℂ] (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N → fullSymRep n) :=
  Rep.coindCosetCoordinates (fullSymRep n) (CongruenceSubgroup.Gamma1 N)

instance fullSymRep_finiteDimensional (n : ℕ) : FiniteDimensional ℂ (fullSymRep n) :=
  Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 2) ℂ n)

instance fullCoinduced_finiteDimensional (N n : ℕ) [NeZero N] :
    FiniteDimensional ℂ (fullCoinduced N n) :=
  FiniteDimensional.of_injective (fullCoinducedCoordinates N n).toLinearMap
    (fullCoinducedCoordinates N n).injective

end MTT.Cohomology

/-! # Trace obstructions to elliptic fixed cosets at large Gamma1 level -/

open scoped MatrixGroups

namespace MTT.Cohomology

theorem trace_conjugate_SL (g x : SL(2, ℤ)) :
    Matrix.trace (x⁻¹ * g * x).val = Matrix.trace g.val := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.trace_mul_cycle, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]

theorem gammaOne_dvd_two_sub_trace {N : ℕ} {g : SL(2, ℤ)}
    (hg : g ∈ CongruenceSubgroup.Gamma1 N) : (N : ℤ) ∣ 2 - Matrix.trace g.val := by
  obtain ⟨ha, hd, _⟩ := (CongruenceSubgroup.Gamma1_mem N g).mp hg
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Int.cast_sub, Int.cast_add,
    Int.cast_ofNat]
  change (2 : ZMod N) - ((g 0 0 : ZMod N) + (g 1 1 : ZMod N)) = 0
  rw [ha, hd]
  ring

theorem gammaOne_coset_smul_ne_of_trace {N : ℕ} (hN : 5 ≤ N) {g : SL(2, ℤ)}
    (ht₁ : -2 ≤ Matrix.trace g.val) (ht₂ : Matrix.trace g.val < 2)
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N) : g • q ≠ q := by
  induction q using Quotient.inductionOn with
  | h x =>
      intro hq
      have hx : x⁻¹ * g * x ∈ CongruenceSubgroup.Gamma1 N := by
        have hx := Quotient.exact hq.symm
        simpa only [QuotientGroup.leftRel_apply, smul_eq_mul, mul_assoc] using hx
      have hd := gammaOne_dvd_two_sub_trace hx
      rw [trace_conjugate_SL] at hd
      have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega :
        0 ≤ 2 - Matrix.trace g.val) (by omega : 2 - Matrix.trace g.val < (N : ℤ)) hd
      omega

end MTT.Cohomology

/-! # The central involution exchanges distinct translation orbits -/

open scoped MatrixGroups

namespace MTT.Cohomology

theorem trace_neg_T_zpow (r : ℤ) :
    Matrix.trace ((-1 : SL(2, ℤ)) * ModularGroup.T ^ r).val = -2 := by
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two, ModularGroup.coe_T_zpow]

theorem gammaOne_central_translation_orbit_ne {N : ℕ} (hN : 5 ≤ N)
    (x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N) :
    (Quotient.mk'' ((-1 : SL(2, ℤ)) • x) :
      MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.T)
        (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N)) ≠ Quotient.mk'' x := by
  intro hx
  obtain ⟨⟨g, hg⟩, hgx⟩ := MulAction.mem_orbit_iff.mp
    (MulAction.orbitRel_apply.mp (Quotient.exact hx))
  obtain ⟨r, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  change (ModularGroup.T ^ r : SL(2, ℤ)) • x = (-1 : SL(2, ℤ)) • x at hgx
  have hfree := gammaOne_coset_smul_ne_of_trace hN
    (g := (-1 : SL(2, ℤ)) * ModularGroup.T ^ r)
    (by rw [trace_neg_T_zpow]) (by rw [trace_neg_T_zpow]; decide) x
  apply hfree
  have hz := congrArg (fun y => (-1 : SL(2, ℤ)) • y) hgx
  simpa only [← mul_smul, neg_mul, one_mul, mul_neg,
    mul_one, neg_neg, one_smul] using hz

end MTT.Cohomology

/-! # Functions supported on one selected smaller orbit in each larger orbit -/

noncomputable section

open scoped Classical

namespace MulAction

variable {G X K V : Type*} [Group G] [MulAction G X] [Field K]
  [AddCommGroup V] [Module K V]

theorem orbit_mk_smul (H : Subgroup G) {g : G} (hg : g ∈ H) (x : X) :
    (Quotient.mk'' (g • x) : orbitRel.Quotient H X) = Quotient.mk'' x := by
  apply Quotient.sound
  exact orbitRel_apply.mpr (mem_orbit_iff.mpr ⟨⟨g, hg⟩, rfl⟩)

def orbitSeed (H J : Subgroup G) (v : V) :
    (orbitRel.Quotient J X → K) →ₗ[K] (X → V) where
  toFun c x := by
    classical
    exact if (Quotient.mk'' x : orbitRel.Quotient H X) =
        Quotient.mk'' (Quotient.mk'' x : orbitRel.Quotient J X).out then
      c (Quotient.mk'' x) • v else 0
  map_add' c d := by
    classical
    funext x
    dsimp
    split_ifs <;> simp [add_smul]
  map_smul' a c := by
    classical
    funext x
    dsimp
    split_ifs <;> simp [mul_smul]

theorem orbitSeed_apply (H J : Subgroup G) (v : V) (c : orbitRel.Quotient J X → K)
    (x : X) : orbitSeed H J v c x =
      if (Quotient.mk'' x : orbitRel.Quotient H X) =
          Quotient.mk'' (Quotient.mk'' x : orbitRel.Quotient J X).out then
        c (Quotient.mk'' x) • v else 0 := by classical exact rfl

theorem orbitSeed_out (H J : Subgroup G) (v : V) (c : orbitRel.Quotient J X → K)
    (d : orbitRel.Quotient J X) : orbitSeed H J v c d.out = c d • v := by
  classical
  have hd : (Quotient.mk'' d.out : orbitRel.Quotient J X) = d := Quotient.out_eq d
  rw [orbitSeed_apply, hd, ite_eq_left rfl]

theorem orbitSeed_smul (H J : Subgroup G) (hHJ : H ≤ J) (v : V)
    (c : orbitRel.Quotient J X → K) {g : G} (hg : g ∈ H) (x : X) :
    orbitSeed H J v c (g • x) = orbitSeed H J v c x := by
  classical
  simp only [orbitSeed_apply, orbit_mk_smul H hg, orbit_mk_smul J (hHJ hg)]

theorem orbitSeed_smul_out_eq_zero (H J : Subgroup G) (v : V)
    (c : orbitRel.Quotient J X → K) {z : G} (hz : z ∈ J)
    (hfree : ∀ x : X, (Quotient.mk'' (z • x) : orbitRel.Quotient H X) ≠ Quotient.mk'' x)
    (d : orbitRel.Quotient J X) : orbitSeed H J v c (z • d.out) = 0 := by
  classical
  have hd : (Quotient.mk'' d.out : orbitRel.Quotient J X) = d := Quotient.out_eq d
  rw [orbitSeed_apply, orbit_mk_smul J hz, hd, ite_eq_right (hfree d.out)]

end MulAction

/-! # Projecting parabolic cocycles to the central fixed subrepresentation

For the large-level dimension count, the whole coinduced module need not have
trivial central action. Averaging at a central involution changes a cocycle by
a principal cocycle and takes values in the fixed subrepresentation.
-/

noncomputable section

namespace Rep

variable {G : Type} [Group G] (A : Rep ℂ G) (z : G)
  (hz : ∀ g, z * g = g * z) (hz₂ : z * z = 1)

def centralAverage : A →ₗ[ℂ] centralFixedRep A z hz where
  toFun v := ⟨(2 : ℂ)⁻¹ • (v + A.ρ z v), by
    rw [mem_centralFixed, map_smul, map_add]
    have hzz : A.ρ z (A.ρ z v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, hz₂, map_one]
      rfl
    rw [hzz, add_comm]⟩
  map_add' v w := by
    apply Subtype.ext
    change (2 : ℂ)⁻¹ • (v + w + A.ρ z (v + w)) =
      (2 : ℂ)⁻¹ • (v + A.ρ z v) + (2 : ℂ)⁻¹ • (w + A.ρ z w)
    rw [map_add]
    module
  map_smul' a v := by
    apply Subtype.ext
    change (2 : ℂ)⁻¹ • (a • v + A.ρ z (a • v)) =
      a • ((2 : ℂ)⁻¹ • (v + A.ρ z v))
    rw [map_smul]
    module

theorem centralAverage_comm (g : G) (v : A) :
    centralAverage A z hz hz₂ (A.ρ g v) =
      (centralFixedRep A z hz).ρ g (centralAverage A z hz hz₂ v) := by
  apply Subtype.ext
  change (2 : ℂ)⁻¹ • (A.ρ g v + A.ρ z (A.ρ g v)) =
    A.ρ g ((2 : ℂ)⁻¹ • (v + A.ρ z v))
  rw [map_smul, map_add, ← Module.End.mul_apply, ← map_mul, hz,
    map_mul, Module.End.mul_apply]

end Rep

/-! # Independent central-fixed translation invariants from cusp orbits -/

noncomputable section

open scoped MatrixGroups Classical

namespace MTT.Cohomology

abbrev translationOrbits (N : ℕ) :=
  MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.T)
    (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N)

abbrev signedTranslationOrbits (N : ℕ) :=
  MulAction.orbitRel.Quotient
    (Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ))
      (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N)

def fullXPower (n : ℕ) : fullSymRep n :=
  ⟨MvPolynomial.X 0 ^ n, MvPolynomial.isHomogeneous_X_pow 0 n⟩

theorem fullXPower_ne_zero (n : ℕ) : fullXPower n ≠ 0 := by
  intro h
  exact pow_ne_zero n (MvPolynomial.X_ne_zero (0 : Fin 2)) (congrArg Subtype.val h)

theorem fullXPower_T (n : ℕ) : (fullSymRep n).ρ ModularGroup.T (fullXPower n) =
    fullXPower n := by
  apply Subtype.ext
  change MvPolynomial.aeval _ (MvPolynomial.X 0 ^ n : Binary ℂ) = _
  simp [ModularGroup.T, Fin.sum_univ_two, fullXPower]

theorem fullCoinducedCoordinates_action (N n : ℕ) (g : SL(2, ℤ))
    (v : fullCoinduced N n) (x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N) :
    fullCoinducedCoordinates N n ((fullCoinduced N n).ρ g v) x =
      (fullSymRep n).ρ g (fullCoinducedCoordinates N n v (g⁻¹ • x)) :=
  Rep.coindCosetCoordinates_action _ _ _ _ _

def coinducedCuspSeed (N n : ℕ) : (signedTranslationOrbits N → ℂ) →ₗ[ℂ]
    fullCoinduced N n :=
  (fullCoinducedCoordinates N n).symm.toLinearMap.comp
    (MulAction.orbitSeed (Subgroup.zpowers ModularGroup.T)
      (Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) (fullXPower n))

theorem coinducedCuspSeed_coordinates (N n : ℕ) (c : signedTranslationOrbits N → ℂ) :
    fullCoinducedCoordinates N n (coinducedCuspSeed N n c) =
      MulAction.orbitSeed (Subgroup.zpowers ModularGroup.T)
        (Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) (fullXPower n) c :=
  (fullCoinducedCoordinates N n).apply_symm_apply _

theorem coinducedCuspSeed_T (N n : ℕ) (c : signedTranslationOrbits N → ℂ) :
    (fullCoinduced N n).ρ ModularGroup.T (coinducedCuspSeed N n c) =
      coinducedCuspSeed N n c := by
  apply (fullCoinducedCoordinates N n).injective
  funext x
  rw [fullCoinducedCoordinates_action, coinducedCuspSeed_coordinates]
  rw [MulAction.orbitSeed_smul (Subgroup.zpowers ModularGroup.T)
    (Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) le_sup_left
    (fullXPower n) c ((Subgroup.zpowers ModularGroup.T).inv_mem
      (Subgroup.mem_zpowers _)) x]
  rw [MulAction.orbitSeed_apply (Subgroup.zpowers ModularGroup.T)
    (Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) (fullXPower n) c x]
  split_ifs <;> simp only [map_smul, fullXPower_T, map_zero]

def centralCuspSeed (N n : ℕ) : (signedTranslationOrbits N → ℂ) →ₗ[ℂ]
    centralCoinduced N n :=
  (Rep.centralAverage (fullCoinduced N n) (-1) neg_one_central (by simp)).comp
    (coinducedCuspSeed N n)

theorem centralCuspSeed_T (N n : ℕ) (c : signedTranslationOrbits N → ℂ) :
    (centralCoinduced N n).ρ ModularGroup.T (centralCuspSeed N n c) =
      centralCuspSeed N n c := by
  have h := Rep.centralAverage_comm (fullCoinduced N n) (-1) neg_one_central
    (by simp) ModularGroup.T (coinducedCuspSeed N n c)
  rw [coinducedCuspSeed_T] at h
  exact h.symm

theorem centralCuspSeed_evaluate {N n : ℕ} (hN : 5 ≤ N)
    (c : signedTranslationOrbits N → ℂ) (d : signedTranslationOrbits N) :
    fullCoinducedCoordinates N n (centralCuspSeed N n c).val d.out =
      (2 : ℂ)⁻¹ • (c d • fullXPower n) := by
  change fullCoinducedCoordinates N n ((2 : ℂ)⁻¹ •
    (coinducedCuspSeed N n c + (fullCoinduced N n).ρ (-1) (coinducedCuspSeed N n c)))
      d.out = _
  rw [map_smul, map_add]
  change (2 : ℂ)⁻¹ • (fullCoinducedCoordinates N n (coinducedCuspSeed N n c) d.out +
    fullCoinducedCoordinates N n ((fullCoinduced N n).ρ (-1) (coinducedCuspSeed N n c))
      d.out) = _
  rw [fullCoinducedCoordinates_action, coinducedCuspSeed_coordinates]
  erw [MulAction.orbitSeed_out (Subgroup.zpowers ModularGroup.T)
      (Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) (fullXPower n) c d]
  have hz : (-1 : SL(2, ℤ))⁻¹ = -1 := by decide
  rw [hz]
  erw [MulAction.orbitSeed_smul_out_eq_zero (Subgroup.zpowers ModularGroup.T)
    (Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) (fullXPower n) c
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) (gammaOne_central_translation_orbit_ne hN) d,
    map_zero, add_zero]

def centralCuspSeedFixed (N n : ℕ) : (signedTranslationOrbits N → ℂ) →ₗ[ℂ]
    ((centralCoinduced N n).ρ ModularGroup.T - LinearMap.id).ker :=
  (centralCuspSeed N n).codRestrict _ fun c => sub_eq_zero.mpr (centralCuspSeed_T N n c)

theorem centralCuspSeedFixed_injective {N n : ℕ} (hN : 5 ≤ N) :
    Function.Injective (centralCuspSeedFixed N n) := by
  intro c e h
  funext d
  have hd := congrArg (fun v => fullCoinducedCoordinates N n v.val.val d.out) h
  change fullCoinducedCoordinates N n (centralCuspSeed N n c).val d.out =
    fullCoinducedCoordinates N n (centralCuspSeed N n e).val d.out at hd
  rw [centralCuspSeed_evaluate hN, centralCuspSeed_evaluate hN] at hd
  have h' := congrArg (fun v => (2 : ℂ) • v) hd
  simp only [smul_smul, ← mul_assoc, mul_inv_cancel₀ (by norm_num : (2 : ℂ) ≠ 0),
    one_mul] at h'
  exact smul_left_injective ℂ (fullXPower_ne_zero n) h'

theorem signedTranslationOrbits_le_T_fixed {N n : ℕ} (hN : 5 ≤ N) :
    Nat.card (signedTranslationOrbits N) ≤
      Module.finrank ℂ ((centralCoinduced N n).ρ ModularGroup.T - LinearMap.id).ker := by
  have : NeZero N := ⟨by omega⟩
  let := Fintype.ofFinite (signedTranslationOrbits N)
  have hd := LinearMap.finrank_le_finrank_of_injective (centralCuspSeedFixed_injective (n := n) hN)
  simpa only [Module.finrank_pi, Fintype.card_eq_nat_card] using hd

end MTT.Cohomology

/-! # From subgroup orbits of left cosets to double cosets by inversion -/

noncomputable section

namespace DoubleCoset

variable {G : Type*} [Group G] (H K : Subgroup G)

def ofLeftCoset : G ⧸ H → Quotient (H : Set G) (K : Set G) :=
  _root_.Quotient.lift (s := QuotientGroup.leftRel H) (fun g => mk H K g⁻¹) (by
    intro a b hab
    change (QuotientGroup.leftRel H) a b at hab
    rw [QuotientGroup.leftRel_apply] at hab
    apply (eq (H := H) (K := K)).mpr
    exact ⟨b⁻¹ * a, by simpa using H.inv_mem hab, 1, K.one_mem, by simp⟩)

theorem ofLeftCoset_smul {g : G} (hg : g ∈ K) (x : G ⧸ H) :
    ofLeftCoset H K (g • x) = ofLeftCoset H K x := by
  induction x using _root_.Quotient.inductionOn with
  | h a =>
      change mk H K (g * a)⁻¹ = mk H K a⁻¹
      symm
      apply (eq (H := H) (K := K)).mpr
      exact ⟨1, H.one_mem, g⁻¹, K.inv_mem hg, by simp⟩

def ofLeftCosetOrbit : MulAction.orbitRel.Quotient K (G ⧸ H) →
    Quotient (H : Set G) (K : Set G) :=
  _root_.Quotient.lift (ofLeftCoset H K) (by
    intro a b hab
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hab)
    rw [← hg]
    exact ofLeftCoset_smul H K g.property b)

theorem ofLeftCosetOrbit_surjective : Function.Surjective (ofLeftCosetOrbit H K) := by
  intro q
  refine ⟨_root_.Quotient.mk'' (QuotientGroup.mk q.out⁻¹ : G ⧸ H), ?_⟩
  change mk H K (q.out⁻¹)⁻¹ = q
  rw [inv_inv, out_eq']

theorem card_le_card_leftCosetOrbits [H.FiniteIndex] :
    Nat.card (Quotient (H : Set G) (K : Set G)) ≤
      Nat.card (MulAction.orbitRel.Quotient K (G ⧸ H)) :=
  Nat.card_le_card_of_surjective _ (ofLeftCosetOrbit_surjective H K)

end DoubleCoset

/-! # The cusp lower bound for central coinduced translation invariants -/

open scoped MatrixGroups

namespace MTT.Cohomology

theorem solution {N n : ℕ} (hN : 5 ≤ N) (_hn : 0 < n) :
    Nat.card (DoubleCoset.Quotient (CongruenceSubgroup.Gamma1 N : Set SL(2, ℤ))
      ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) :
        Set SL(2, ℤ))) ≤
      Module.finrank ℂ ((centralCoinduced N n).ρ ModularGroup.T - LinearMap.id).ker := by
  have : NeZero N := ⟨by omega⟩
  exact (DoubleCoset.card_le_card_leftCosetOrbits (CongruenceSubgroup.Gamma1 N)
    (Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1))).trans
      (signedTranslationOrbits_le_T_fixed (n := n) hN)

end MTT.Cohomology

export MTT.Cohomology (solution)
