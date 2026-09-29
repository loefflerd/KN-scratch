import Mathlib
import Definitions.MTT.Def_MTT_NormalizedParabolicCocycles
import Definitions.MTT.Def_MTT_LevelOnePeriodRelations
import Theorems.MTT.Thm_MTT_Cohomology_normalizedParabolic_finrank
import Theorems.FLT.Thm_CongruenceSubgroup_closure_T_U_neg_one_eq_Gamma0_three

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups

namespace MTT.Cohomology

open MvPolynomial

theorem mem_sup_neg_one_iff (H : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) :
    g ∈ H ⊔ Subgroup.zpowers (-1) ↔ g ∈ H ∨ -g ∈ H := by
  let K : Subgroup SL(2, ℤ) :=
    { carrier := {g | g ∈ H ∨ -g ∈ H}
      one_mem' := Or.inl H.one_mem
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (H.mul_mem ha hb)
        · exact Or.inr (by simpa using H.mul_mem ha hb)
        · exact Or.inr (by simpa using H.mul_mem ha hb)
        · exact Or.inl (by simpa using H.mul_mem ha hb)
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (H.inv_mem ha)
        · exact Or.inr (by simpa using H.inv_mem ha) }
  have hle : H ⊔ Subgroup.zpowers (-1) ≤ K := by
    refine sup_le (fun _ h => Or.inl h) (Subgroup.zpowers_le.mpr ?_)
    exact Or.inr (by simpa only [neg_neg] using H.one_mem)
  refine ⟨fun h => hle h, ?_⟩
  rintro (h | h)
  · exact Subgroup.mem_sup_left h
  · have hm := Subgroup.mul_mem_sup h (Subgroup.mem_zpowers (-1 : SL(2, ℤ)))
    simpa using hm

end MTT.Cohomology

namespace MTT.Cohomology

open MvPolynomial

theorem gammaOne_neg_one_not_mem_of_three_le {N : ℕ} (hN : 3 ≤ N) :
    (-1 : SL(2, ℤ)) ∉ CongruenceSubgroup.Gamma1 N := by
  intro h
  have ha := ((CongruenceSubgroup.Gamma1_mem N _).mp h).1
  have hc : ((-1 : ℤ) : ZMod N) = (1 : ℤ) := by simpa using ha
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub (-1) 1 N).mp hc
  have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt (by norm_num : (0 : ℤ) ≤ 1 - -1)
    (by omega : (1 : ℤ) - -1 < N) hd
  norm_num at hz

end MTT.Cohomology

/-! # Translation and an elliptic generator at level three -/

open scoped MatrixGroups

namespace MTT.Cohomology

def gammaOneThreeLower : CongruenceSubgroup.Gamma1 3 :=
  ⟨⟨!![1, 0; -3, 1], by norm_num [Matrix.det_fin_two]⟩,
    (CongruenceSubgroup.Gamma1_mem 3 _).mpr (by decide)⟩

def gammaOneThreeElliptic : CongruenceSubgroup.Gamma1 3 :=
  gammaOneT 3 * gammaOneThreeLower

theorem gammaOne_three_closure :
    Subgroup.closure ({ModularGroup.T, gammaOneThreeLower.val} : Set SL(2, ℤ)) =
      CongruenceSubgroup.Gamma1 3 := by
  let H := Subgroup.closure ({ModularGroup.T, gammaOneThreeLower.val} : Set SL(2, ℤ))
  have hH : H ≤ CongruenceSubgroup.Gamma1 3 := by
    apply (Subgroup.closure_le _).mpr
    rintro g (rfl | rfl)
    · exact (gammaOneT 3).property
    · exact gammaOneThreeLower.property
  have hG : CongruenceSubgroup.Gamma0 3 ≤ H ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) := by
    rw [← CongruenceSubgroup.closure_T_U_neg_one_eq_Gamma0_three gammaOneThreeLower.val rfl]
    apply (Subgroup.closure_le _).mpr
    rintro g (rfl | rfl | rfl)
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (Or.inl rfl))
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (Or.inr rfl))
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  refine le_antisymm hH fun g hg => ?_
  rcases (mem_sup_neg_one_iff H g).mp (hG (CongruenceSubgroup.Gamma1_in_Gamma0 3 hg)) with h | h
  · exact h
  · exfalso
    apply gammaOne_neg_one_not_mem_of_three_le (by decide : 3 ≤ 3)
    have hm := (CongruenceSubgroup.Gamma1 3).mul_mem (hH h)
      ((CongruenceSubgroup.Gamma1 3).inv_mem hg)
    simpa only [neg_mul, mul_inv_cancel] using hm

theorem gammaOne_three_generators :
    Subgroup.closure ({gammaOneT 3, gammaOneThreeLower} :
      Set (CongruenceSubgroup.Gamma1 3)) = ⊤ := by
  apply Subgroup.map_injective (CongruenceSubgroup.Gamma1 3).subtype_injective
  rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton]
  change Subgroup.closure ({ModularGroup.T, gammaOneThreeLower.val} : Set SL(2, ℤ)) = _
  rw [gammaOne_three_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem gammaOneThreeElliptic_cube : gammaOneThreeElliptic ^ 3 = 1 := by
  apply Subtype.ext
  decide

end MTT.Cohomology

/-!
# Finite-dimensional one-cocycles

A one-cocycle is determined by its values on group generators. Restriction to
a finite generating set therefore embeds the cocycle space into a finite power
of the coefficient module. This is the finite-generation input for the MTT
parabolic-cohomology dimension argument; it assumes no Eichler–Shimura theorem.
-/

noncomputable section

universe u

namespace groupCohomology

variable {K G : Type u} [Field K] [Group G] {A : Rep K G}

/-- One-cocycles agreeing on a generating set agree everywhere. -/
theorem cocycles₁_ext_of_generators {s : Set G} (hs : Subgroup.closure s = ⊤)
    {f g : cocycles₁ A} (hfg : ∀ x ∈ s, f x = g x) : f = g := by
  apply cocycles₁_ext
  intro x
  have hx : x ∈ Subgroup.closure s := hs ▸ Subgroup.mem_top x
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hfg x hx
  | one => simp only [cocycles₁_map_one]
  | mul x y _ _ hx hy =>
      rw [(mem_cocycles₁_iff f).1 f.property,
        (mem_cocycles₁_iff g).1 g.property, hx, hy]
  | inv x _ hx =>
      have hf := (mem_cocycles₁_iff f).1 f.property x⁻¹ x
      have hg := (mem_cocycles₁_iff g).1 g.property x⁻¹ x
      simp only [inv_mul_cancel, cocycles₁_map_one, hx] at hf hg
      exact add_left_cancel (hf.symm.trans hg)

end groupCohomology

/-! # Finite coordinates for binary homogeneous polynomials -/

noncomputable section

namespace MTT.Cohomology

def homogeneousExponentEquiv (n : ℕ) :
    {d : Fin 2 →₀ ℕ // d.degree = n} ≃ Fin (n + 1) where
  toFun d := ⟨d.val 0, by
    have hd := d.property
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hd
    omega⟩
  invFun j := ⟨Finsupp.equivFunOnFinite.symm ![j.val, n - j.val], by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
    change j.val + (n - j.val) = n
    omega⟩
  left_inv d := by
    apply Subtype.ext
    ext i
    have hd := d.property
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hd
    change (![d.val 0, n - d.val 0] : Fin 2 → ℕ) i = d.val i
    fin_cases i
    · rfl
    · change n - d.val 0 = d.val 1
      omega
  right_inv j := by
    apply Fin.ext
    rfl

def symmetricPowerCoordinates (R : Type*) [CommRing R] (n : ℕ) :
    Sym R n ≃ₗ[R] (Fin (n + 1) →₀ R) :=
  (LinearEquiv.ofEq _ _ (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (Fin 2) R n))
    ≪≫ₗ AddMonoidAlgebra.supportedEquivFinsupp _
    ≪≫ₗ Finsupp.domLCongr (homogeneousExponentEquiv n)

theorem finrank_sym (n : ℕ) : Module.finrank ℂ (Sym ℂ n) = n + 1 := by
  rw [(symmetricPowerCoordinates ℂ n).finrank_eq, Module.finrank_finsupp_self, Fintype.card_fin]

def symmetricPowerBasis (R : Type*) [CommRing R] (n : ℕ) :
    Module.Basis (Fin (n + 1)) R (Sym R n) :=
  Module.Basis.ofRepr (symmetricPowerCoordinates R n)

@[simp]
theorem symmetricPowerBasis_repr (R : Type*) [CommRing R] (n : ℕ) :
    (symmetricPowerBasis R n).repr = symmetricPowerCoordinates R n := rfl

theorem symmetricPowerCoordinates_apply {R : Type*} [CommRing R] {n : ℕ}
    (P : Sym R n) (j : Fin (n + 1)) :
    symmetricPowerCoordinates R n P j =
      AddMonoidAlgebra.coeff P.val (homogeneousExponentEquiv n |>.symm j).val := by
  rfl

theorem symmetricPowerBasis_val {R : Type*} [CommRing R] {n : ℕ} (j : Fin (n + 1)) :
    (symmetricPowerBasis R n j).val =
      MvPolynomial.monomial (homogeneousExponentEquiv n |>.symm j).val 1 := by
  classical
  let Q : Sym R n := ⟨MvPolynomial.monomial ((homogeneousExponentEquiv n).symm j).val 1,
    MvPolynomial.isHomogeneous_monomial 1 ((homogeneousExponentEquiv n).symm j).property⟩
  have h : symmetricPowerBasis R n j = Q := by
    apply (symmetricPowerCoordinates R n).injective
    ext i
    change (symmetricPowerBasis R n).repr (symmetricPowerBasis R n j) i = _
    rw [Module.Basis.repr_self_apply, symmetricPowerCoordinates_apply]
    simp [Q, MvPolynomial.coeff_monomial, Subtype.val_inj]
  exact congrArg Subtype.val h

theorem symmetricPowerBasis_val_eq {R : Type*} [CommRing R] {n : ℕ}
    (j : Fin (n + 1)) : (symmetricPowerBasis R n j).val =
      MvPolynomial.X 0 ^ j.val * MvPolynomial.X 1 ^ (n - j.val) := by
  rw [symmetricPowerBasis_val, MvPolynomial.monomial_eq]
  simp [homogeneousExponentEquiv, Finsupp.prod_fintype, Fin.prod_univ_two]

theorem symmetricPower_expansion {R : Type*} [CommRing R] {n : ℕ} (P : Sym R n) :
    P.val = ∑ j : Fin (n + 1), symmetricPowerCoordinates R n P j •
      (MvPolynomial.X 0 ^ j.val * MvPolynomial.X 1 ^ (n - j.val)) := by
  have h := congrArg Subtype.val ((symmetricPowerBasis R n).sum_repr P)
  simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower, symmetricPowerBasis_val_eq,
    symmetricPowerBasis_repr]
    using h.symm

end MTT.Cohomology

/-! # Invertible linear substitutions on binary symmetric powers -/

noncomputable section

namespace MTT.Cohomology

open MvPolynomial

variable {K : Type*} [Field K]

local instance (n : ℕ) : FiniteDimensional K (Sym K n) :=
  Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 2) K n)

def binaryLinearChange (a b c d : K) : Binary K →ₐ[K] Binary K :=
  MvPolynomial.aeval ![a • X 0 + b • X 1, c • X 0 + d • X 1]

theorem binaryLinearChange_comp (a b c d e f g h : K) :
    (binaryLinearChange a b c d).comp (binaryLinearChange e f g h) =
      binaryLinearChange (e * a + f * c) (e * b + f * d) (g * a + h * c) (g * b + h * d) := by
  ext i : 1
  fin_cases i <;> simp [binaryLinearChange] <;> module

theorem binaryLinearChange_one : binaryLinearChange (1 : K) 0 0 1 = AlgHom.id K _ := by
  ext i : 1
  fin_cases i <;> simp [binaryLinearChange]

theorem binaryLinearChange_mem_sym (a b c d : K) {n : ℕ} (P : Sym K n) :
    binaryLinearChange a b c d P.val ∈ Sym K n := by
  have hg (i : Fin 2) :
      (![a • X 0 + b • X 1, c • X 0 + d • X 1] i : Binary K).IsHomogeneous 1 := by
    fin_cases i <;>
      exact (Sym K 1).add_mem ((Sym K 1).smul_mem _ (isHomogeneous_X _ _))
        ((Sym K 1).smul_mem _ (isHomogeneous_X _ _))
  change (MvPolynomial.aeval
    (![a • X 0 + b • X 1, c • X 0 + d • X 1] : Fin 2 → Binary K) P.val).IsHomogeneous n
  simpa only [one_mul] using P.property.aeval _ hg

def symmetricPowerChange (a b c d : K) (n : ℕ) : Sym K n →ₗ[K] Sym K n where
  toFun P := ⟨binaryLinearChange a b c d P.val, binaryLinearChange_mem_sym a b c d P⟩
  map_add' P Q := Subtype.ext (map_add _ P.val Q.val)
  map_smul' a P := Subtype.ext (map_smul _ a P.val)

theorem symmetricPowerChange_comp (a b c d e f g h : K) (n : ℕ) :
    (symmetricPowerChange a b c d n).comp (symmetricPowerChange e f g h n) =
      symmetricPowerChange (e * a + f * c) (e * b + f * d) (g * a + h * c) (g * b + h * d) n := by
  apply LinearMap.ext
  intro P
  apply Subtype.ext
  exact congrArg (fun F : Binary K →ₐ[K] Binary K => F P.val)
    (binaryLinearChange_comp a b c d e f g h)

theorem symmetricPowerChange_one (n : ℕ) :
    symmetricPowerChange (1 : K) 0 0 1 n = LinearMap.id := by
  apply LinearMap.ext
  intro P
  apply Subtype.ext
  exact congrArg (fun F : Binary K →ₐ[K] Binary K => F P.val) binaryLinearChange_one

theorem symmetricPowerChange_left_inverse (a b c d : K) (hdet : a * d - b * c ≠ 0)
    (n : ℕ) :
    (symmetricPowerChange (d / (a * d - b * c)) (-b / (a * d - b * c))
      (-c / (a * d - b * c)) (a / (a * d - b * c)) n).comp
        (symmetricPowerChange a b c d n) = LinearMap.id := by
  rw [symmetricPowerChange_comp]
  have h₁ : a * (d / (a * d - b * c)) + b * (-c / (a * d - b * c)) = 1 := by
    field_simp [hdet]
    ring
  have h₂ : a * (-b / (a * d - b * c)) + b * (a / (a * d - b * c)) = 0 := by ring
  have h₃ : c * (d / (a * d - b * c)) + d * (-c / (a * d - b * c)) = 0 := by ring
  have h₄ : c * (-b / (a * d - b * c)) + d * (a / (a * d - b * c)) = 1 := by
    calc
      _ = a * (d / (a * d - b * c)) + b * (-c / (a * d - b * c)) := by ring
      _ = 1 := h₁
  rw [h₁, h₂, h₃, h₄, symmetricPowerChange_one]

def symmetricPowerChangeEquiv (a b c d : K) (hdet : a * d - b * c ≠ 0) (n : ℕ) :
    Sym K n ≃ₗ[K] Sym K n :=
  LinearEquiv.ofInjectiveEndo (symmetricPowerChange a b c d n) (by
    have hi := symmetricPowerChange_left_inverse a b c d hdet n
    intro P Q h
    have h' := congrArg (symmetricPowerChange (d / (a * d - b * c))
      (-b / (a * d - b * c)) (-c / (a * d - b * c)) (a / (a * d - b * c)) n) h
    simpa only [← LinearMap.comp_apply, hi, LinearMap.id_apply] using h')

theorem symmetricPowerChangeEquiv_apply (a b c d : K) (hdet : a * d - b * c ≠ 0)
    (n : ℕ) (P : Sym K n) :
    symmetricPowerChangeEquiv a b c d hdet n P = symmetricPowerChange a b c d n P := rfl

theorem symmetricPowerChange_basis_val (a b c d : K) {n : ℕ} (j : Fin (n + 1)) :
    (symmetricPowerChange a b c d n (symmetricPowerBasis K n j)).val =
      (a • X 0 + b • X 1) ^ j.val * (c • X 0 + d • X 1) ^ (n - j.val) := by
  change binaryLinearChange a b c d (symmetricPowerBasis K n j).val = _
  rw [symmetricPowerBasis_val_eq]
  simp [binaryLinearChange]

end MTT.Cohomology

namespace MTT.Cohomology

open MvPolynomial

theorem bind_smul_X_of_homogeneous {R : Type*} [CommRing R] {n : ℕ}
    {P : Binary R} (hP : P.IsHomogeneous n) (a : R) :
    bind₁ (fun i => a • X i) P = a ^ n • P := by
  classical
  induction hP using IsWeightedHomogeneous.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add P Q hP hQ ihP ihQ => rw [map_add, ihP, ihQ, smul_add]
  | monomial d r hd =>
      rw [bind₁_monomial]
      simp only [Algebra.smul_def, algebraMap_eq, mul_pow, Finset.prod_mul_distrib,
        ← map_pow, ← map_prod]
      rw [Finset.prod_pow_eq_pow_sum]
      have hdeg : ∑ i ∈ d.support, d i = n := by
        simpa only [Finsupp.weight_apply, Finsupp.sum,
          Pi.one_apply, smul_eq_mul, mul_one] using hd
      rw [hdeg, monomial_eq, Finsupp.prod]
      ring

theorem act_neg_one_of_homogeneous {R : Type*} [CommRing R] {n : ℕ}
    {P : Binary R} (hP : P ∈ Sym R n) : act (-1) P = (-1 : R) ^ n • P := by
  change bind₁ (fun i : Fin 2 => ∑ a : Fin 2,
    ((-1 : Matrix (Fin 2) (Fin 2) ℤ) a i : R) • X a) P = _
  have hvars : (fun i : Fin 2 => ∑ a : Fin 2,
      ((-1 : Matrix (Fin 2) (Fin 2) ℤ) a i : R) • X a) =
      (fun i : Fin 2 => (-1 : R) • (X i : Binary R)) := by
    funext i
    fin_cases i <;> simp [Matrix.one_apply]
  rw [hvars]
  exact bind_smul_X_of_homogeneous hP (-1)

end MTT.Cohomology

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

namespace LinearMap

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

theorem range_cubic_norm_eq_ker_sub_id (r : V →ₗ[K] V) (hr : ∀ P, r (r (r P)) = P) :
    (r ^ 2 + r + LinearMap.id).range = (r - LinearMap.id).ker := by
  ext P
  rw [mem_ker, sub_apply, id_apply, sub_eq_zero]
  constructor
  · rintro ⟨Q, rfl⟩
    simp only [add_apply, id_apply, pow_two, Module.End.mul_apply, map_add, hr]
    module
  · intro h
    refine ⟨(3 : K)⁻¹ • P, ?_⟩
    simp only [add_apply, id_apply, pow_two, Module.End.mul_apply, map_smul, h]
    module


end LinearMap

/-! # The order-three fixed-space dimension -/

noncomputable section

namespace LinearMap

theorem three_mul_finrank_fixed_eq_trace {K V : Type*} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (r : Module.End K V) (hr : ∀ P, r (r (r P)) = P) :
    (3 : K) * Module.finrank K (r - LinearMap.id).ker =
      Module.finrank K V + LinearMap.trace K V r + LinearMap.trace K V (r ^ 2) := by
  have hp : LinearMap.IsProj (r - LinearMap.id).ker
      ((3 : K)⁻¹ • (r ^ 2 + r + LinearMap.id)) := by
    constructor
    · intro P
      change r ((3 : K)⁻¹ • (r (r P) + r P + P)) -
        (3 : K)⁻¹ • (r (r P) + r P + P) = 0
      rw [map_smul, map_add, map_add, hr P]
      module
    · intro P hP
      have h : r P = P := sub_eq_zero.mp hP
      change (3 : K)⁻¹ • (r (r P) + r P + P) = P
      simp only [h]
      module
  have ht := hp.trace
  rw [map_smul, map_add, map_add, LinearMap.trace_id, smul_eq_mul] at ht
  linear_combination -3 * ht

end LinearMap

namespace MTT.Cohomology

open MvPolynomial

theorem act_ST_linear_form (a : ℂ) (ha : a ^ 2 - a + 1 = 0) :
    act (ModularGroup.S * ModularGroup.T).val (X 0 - a • X 1 : Binary ℂ) =
      a • (X 0 - a • X 1) := by
  have hST : (ModularGroup.S * ModularGroup.T).val = !![0, -1; 1, 1] := by decide
  have ha' : a * a = a - 1 := by linear_combination ha
  rw [hST]
  simp [act, Fin.sum_univ_two, smul_sub, smul_smul, ha']
  module

def ellipticEigenbasis (a b : ℂ) (hab : a ≠ b) (n : ℕ) :
    Module.Basis (Fin (n + 1)) ℂ (gammaOneRep 1 n) :=
  (symmetricPowerBasis ℂ n).map
    (symmetricPowerChangeEquiv 1 (-a) 1 (-b)
      (by simpa [sub_eq_add_neg, add_comm] using sub_ne_zero.mpr hab) n)

theorem ellipticEigenbasis_val (a b : ℂ) (hab : a ≠ b) {n : ℕ} (j : Fin (n + 1)) :
    (ellipticEigenbasis a b hab n j).val =
      (X 0 - a • X 1) ^ j.val * (X 0 - b • X 1) ^ (n - j.val) := by
  change (symmetricPowerChange 1 (-a) 1 (-b) n (symmetricPowerBasis ℂ n j)).val = _
  simp only [symmetricPowerChange_basis_val, one_smul, neg_smul, ← sub_eq_add_neg]

theorem levelOneAction_ST_eigenbasis (a b : ℂ) (hab : a ≠ b)
    (ha : a ^ 2 - a + 1 = 0) (hb : b ^ 2 - b + 1 = 0) {n : ℕ} (j : Fin (n + 1)) :
    (gammaOneRep 1 n).ρ (levelOneIncl (ModularGroup.S * ModularGroup.T))
      (ellipticEigenbasis a b hab n j) =
        (a ^ j.val * b ^ (n - j.val)) • ellipticEigenbasis a b hab n j := by
  apply Subtype.ext
  change act (ModularGroup.S * ModularGroup.T).val _ = _
  rw [ellipticEigenbasis_val]
  change (MvPolynomial.aeval _)
    ((X 0 - a • X 1) ^ j.val * (X 0 - b • X 1) ^ (n - j.val)) = _
  rw [map_mul, map_pow, map_pow]
  change (act (ModularGroup.S * ModularGroup.T).val (X 0 - a • X 1)) ^ j.val *
    (act (ModularGroup.S * ModularGroup.T).val (X 0 - b • X 1)) ^ (n - j.val) = _
  rw [act_ST_linear_form a ha, act_ST_linear_form b hb]
  change _ = (a ^ j.val * b ^ (n - j.val)) • (ellipticEigenbasis a b hab n j).val
  rw [ellipticEigenbasis_val, smul_pow, smul_pow, smul_mul_smul_comm]

theorem trace_levelOneAction_ST (a b : ℂ) (hab : a ≠ b)
    (ha : a ^ 2 - a + 1 = 0) (hb : b ^ 2 - b + 1 = 0) (n : ℕ) :
    LinearMap.trace ℂ (gammaOneRep 1 n)
      ((gammaOneRep 1 n).ρ (levelOneIncl (ModularGroup.S * ModularGroup.T))) =
        ∑ j : Fin (n + 1), a ^ j.val * b ^ (n - j.val) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (ellipticEigenbasis a b hab n), Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply,
    levelOneAction_ST_eigenbasis a b hab ha hb, map_smul,
    Module.Basis.repr_self_apply, Finsupp.smul_apply, smul_eq_mul, if_true, mul_one]

theorem trace_levelOneAction_ST_sq (a b : ℂ) (hab : a ≠ b)
    (ha : a ^ 2 - a + 1 = 0) (hb : b ^ 2 - b + 1 = 0) (n : ℕ) :
    LinearMap.trace ℂ (gammaOneRep 1 n)
      (((gammaOneRep 1 n).ρ (levelOneIncl (ModularGroup.S * ModularGroup.T))) ^ 2) =
        ∑ j : Fin (n + 1), (a ^ j.val * b ^ (n - j.val)) ^ 2 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (ellipticEigenbasis a b hab n), Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, pow_two, Module.End.mul_apply,
    levelOneAction_ST_eigenbasis a b hab ha hb, map_smul,
    Module.Basis.repr_self_apply, Finsupp.smul_apply, smul_eq_mul, if_true, mul_one]

theorem binaryGeometricSum_mul_sub (a b : ℂ) (n : ℕ) :
    (∑ j : Fin (n + 1), a ^ j.val * b ^ (n - j.val)) * (a - b) =
      a ^ (n + 1) - b ^ (n + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun j => a ^ j * b ^ (n - j))]
  simpa only [Nat.add_sub_cancel] using geom_sum₂_mul a b (n + 1)

theorem binaryGeometricSum_comm (a b : ℂ) (n : ℕ) :
    (∑ j : Fin (n + 1), a ^ j.val * b ^ (n - j.val)) =
      ∑ j : Fin (n + 1), b ^ j.val * a ^ (n - j.val) := by
  rw [Fin.sum_univ_eq_sum_range (fun j => a ^ j * b ^ (n - j)),
    Fin.sum_univ_eq_sum_range (fun j => b ^ j * a ^ (n - j))]
  simpa only [Nat.add_sub_cancel] using geom_sum₂_comm a b (n + 1)

end MTT.Cohomology

namespace MTT.Cohomology

open MvPolynomial

theorem exists_elliptic_eigenvalues :
    ∃ a b : ℂ, a ≠ b ∧ a ^ 2 - a + 1 = 0 ∧ b ^ 2 - b + 1 = 0 ∧ a + b = 1 := by
  let z := Complex.exp (2 * Real.pi * Complex.I / 3)
  have hz : IsPrimitiveRoot z 3 := Complex.isPrimitiveRoot_exp 3 (by decide)
  have hz0 := hz.ne_zero (by decide)
  have hz1 := hz.ne_one (by decide)
  have hz3 : z ^ 3 = 1 := hz.pow_eq_one
  have hs : z ^ 2 + z + 1 = 0 := by
    have h := hz.geom_sum_eq_zero (by decide)
    norm_num [Finset.sum_range_succ] at h
    linear_combination h
  have hz4 : z ^ 4 = z := by
    calc
      _ = z ^ 3 * z := by ring
      _ = z := by rw [hz3, one_mul]
  refine ⟨-z, -(z ^ 2), ?_, ?_, ?_, ?_⟩
  · intro h
    have h' : z * (z - 1) = 0 := by linear_combination h
    exact hz1 (sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left hz0))
  · linear_combination hs
  · linear_combination hs + hz4
  · linear_combination -hs

end MTT.Cohomology

/-! # From degree-zero MTT cocycles to scalar parabolic homomorphisms

The comparison uses only the definitions: degree-zero homogeneous polynomials
are constants, and an integral determinant-one matrix of trace squared four
fixes a rational cusp. No period-map injectivity is used.
-/

noncomputable section

namespace MTT.Cohomology

open Matrix

theorem exists_cusp_fixed_of_trace_sq (g : SpecialLinearGroup (Fin 2) ℤ)
    (hg : g.val.trace ^ 2 = 4) : ∃ x : Cusp, cuspAct g x = x := by
  let a := SpecialLinearGroup.mapGL ℚ g
  by_cases hc : a 1 0 = 0
  · exact ⟨OnePoint.infty, OnePoint.smul_infty_eq_self_iff.mpr hc⟩
  · refine ⟨((a 0 0 - a 1 1) / (2 * a 1 0) : ℚ), ?_⟩
    change a • (((a 0 0 - a 1 1) / (2 * a 1 0) : ℚ) : Cusp) = _
    apply GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff.mp
    have hdet : a 0 0 * a 1 1 - a 0 1 * a 1 0 = 1 := by
      have h := g.property
      rw [det_fin_two] at h
      change (g 0 0 : ℚ) * g 1 1 - g 0 1 * g 1 0 = 1
      exact_mod_cast h
    have htrace : (a 0 0 + a 1 1) ^ 2 = 4 := by
      rw [trace_fin_two] at hg
      change ((g 0 0 : ℚ) + g 1 1) ^ 2 = 4
      exact_mod_cast hg
    simp only [GeneralLinearGroup.fixpointPolynomial, map_sub, map_add, map_mul,
      Polynomial.aeval_X_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_self_apply]
    field_simp
    linear_combination -htrace + 4 * hdet

end MTT.Cohomology

namespace MTT.Cohomology

open MvPolynomial

lemma eval_act (γ : Matrix (Fin 2) (Fin 2) ℤ) (P : Binary ℂ) (u v : ℂ) :
    MvPolynomial.eval ![u, v] (act γ P) =
      MvPolynomial.eval ![(γ 0 0 : ℂ) * u + (γ 1 0 : ℂ) * v,
        (γ 0 1 : ℂ) * u + (γ 1 1 : ℂ) * v] P := by
  simp only [act, MvPolynomial.aeval_def, AlgHom.toLinearMap_apply, MvPolynomial.eval_eval₂]
  congr 1
  · ext c
    simp
  · funext i
    fin_cases i <;> simp [Fin.sum_univ_two, mul_comm]

end MTT.Cohomology

/-! # The elliptic correction in level-three parabolic cohomology -/

noncomputable section

namespace MTT.Cohomology

def levelThreeAction (n : ℕ) : Module.End ℂ (gammaOneRep 3 n) :=
  (gammaOneRep 3 n).ρ gammaOneThreeElliptic

def levelThreeNorm (n : ℕ) : Module.End ℂ (gammaOneRep 3 n) :=
  levelThreeAction n ^ 2 + levelThreeAction n + LinearMap.id

theorem levelThreeAction_cubic (n : ℕ) (P : gammaOneRep 3 n) :
    levelThreeAction n (levelThreeAction n (levelThreeAction n P)) = P := by
  have h : levelThreeAction n ^ 3 = 1 := by
    rw [levelThreeAction, ← map_pow, gammaOneThreeElliptic_cube, map_one]
  exact congrArg (fun f : Module.End ℂ (gammaOneRep 3 n) => f P) h

def normalizedEvalThreeElliptic (n : ℕ) : normalizedParabolic 3 n →ₗ[ℂ] gammaOneRep 3 n :=
  (LinearMap.proj gammaOneThreeElliptic).comp
    ((parabolicCocycles 3 n).subtype.comp (normalizedParabolic 3 n).subtype)

theorem normalizedEvalThreeElliptic_eq (n : ℕ) (c : normalizedParabolic 3 n) :
    normalizedEvalThreeElliptic n c =
      (gammaOneRep 3 n).ρ (gammaOneT 3) (c.val.val gammaOneThreeLower) := by
  have hc := ((mem_parabolicCocycles_iff _).mp c.val.property).1
    (gammaOneT 3) gammaOneThreeLower
  change c.val.val gammaOneThreeElliptic = _
  exact hc.trans (by rw [show c.val.val (gammaOneT 3) = 0 from c.property, add_zero])

theorem normalizedEvalThreeElliptic_injective (n : ℕ) :
    Function.Injective (normalizedEvalThreeElliptic n) := by
  intro c d h
  have hU : c.val.val gammaOneThreeLower = d.val.val gammaOneThreeLower := by
    rw [normalizedEvalThreeElliptic_eq, normalizedEvalThreeElliptic_eq] at h
    have hi : Function.LeftInverse ((gammaOneRep 3 n).ρ (gammaOneT 3)⁻¹)
        ((gammaOneRep 3 n).ρ (gammaOneT 3)) := by
      intro P
      change (((gammaOneRep 3 n).ρ (gammaOneT 3)⁻¹) *
        ((gammaOneRep 3 n).ρ (gammaOneT 3))) P = P
      rw [← map_mul, inv_mul_cancel, map_one]
      rfl
    exact hi.injective h
  have hc : (⟨c.val.val, c.val.property.1⟩ : groupCohomology.cocycles₁ (gammaOneRep 3 n)) =
      ⟨d.val.val, d.val.property.1⟩ := by
    apply groupCohomology.cocycles₁_ext_of_generators gammaOne_three_generators
    rintro g (rfl | rfl)
    · exact c.property.trans d.property.symm
    · exact hU
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : groupCohomology.cocycles₁ (gammaOneRep 3 n) => z.val) hc

theorem normalizedEvalThreeElliptic_mem_ker (n : ℕ) (c : normalizedParabolic 3 n) :
    normalizedEvalThreeElliptic n c ∈ (levelThreeNorm n).ker := by
  have hc := ((mem_parabolicCocycles_iff _).mp c.val.property).1
  have hE : gammaOneThreeElliptic * (gammaOneThreeElliptic * gammaOneThreeElliptic) = 1 := by
    simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using gammaOneThreeElliptic_cube
  have hz : c.val.val 1 = 0 :=
    groupCohomology.cocycles₁_map_one ⟨c.val.val, c.val.property.1⟩
  have h := congrArg c.val.val hE
  rw [hc, hc, map_add, hz] at h
  exact h

def normalizedToThreeNormKernel (n : ℕ) :
    normalizedParabolic 3 n →ₗ[ℂ] (levelThreeNorm n).ker :=
  (normalizedEvalThreeElliptic n).codRestrict _ (normalizedEvalThreeElliptic_mem_ker n)

theorem normalizedThree_eval_zero (n : ℕ) (c : normalizedParabolic 3 n) :
    MvPolynomial.eval ![(1 : ℂ), -1] (normalizedEvalThreeElliptic n c).val = 0 := by
  obtain ⟨x, hx⟩ := exists_cusp_fixed_of_trace_sq gammaOneThreeLower.val (by decide)
  obtain ⟨P, hP⟩ := ((mem_parabolicCocycles_iff _).mp c.val.property).2
    x gammaOneThreeLower hx
  rw [normalizedEvalThreeElliptic_eq, hP]
  change MvPolynomial.eval ![(1 : ℂ), -1]
    (act ModularGroup.T.val (act !![1, 0; -3, 1] P.val - P.val)) = 0
  rw [eval_act]
  simp [ModularGroup.T, MvPolynomial.eval_sub, eval_act]

def levelThreeKernelWitness (n : ℕ) : gammaOneRep 3 n :=
  levelThreeAction n ⟨MvPolynomial.X 1 ^ n, MvPolynomial.isHomogeneous_X_pow 1 n⟩ -
    ⟨MvPolynomial.X 1 ^ n, MvPolynomial.isHomogeneous_X_pow 1 n⟩

theorem levelThreeKernelWitness_mem_ker (n : ℕ) :
    levelThreeKernelWitness n ∈ (levelThreeNorm n).ker := by
  have h (P : gammaOneRep 3 n) :
      levelThreeNorm n (levelThreeAction n P - P) = 0 := by
    simp only [levelThreeNorm, LinearMap.add_apply, LinearMap.id_apply,
      pow_two, Module.End.mul_apply, map_sub, levelThreeAction_cubic]
    module
  exact h _

theorem levelThreeKernelWitness_eval {n : ℕ} (hn : 0 < n) :
    MvPolynomial.eval ![(1 : ℂ), -1] (levelThreeKernelWitness n).val ≠ 0 := by
  change MvPolynomial.eval ![(1 : ℂ), -1]
    (act (gammaOneThreeElliptic.val.val) (MvPolynomial.X 1 ^ n) - MvPolynomial.X 1 ^ n) ≠ 0
  have hE : gammaOneThreeElliptic.val.val = !![-2, 1; -3, 1] := by decide
  rw [hE]
  simp [MvPolynomial.eval_sub, eval_act, Nat.ne_of_gt hn]

theorem normalizedToThreeNormKernel_not_surjective {n : ℕ} (hn : 0 < n) :
    ¬ Function.Surjective (normalizedToThreeNormKernel n) := by
  intro h
  obtain ⟨c, hc⟩ := h ⟨levelThreeKernelWitness n, levelThreeKernelWitness_mem_ker n⟩
  have he := congrArg Subtype.val hc
  have hz := normalizedThree_eval_zero n c
  change normalizedEvalThreeElliptic n c = levelThreeKernelWitness n at he
  rw [he] at hz
  exact levelThreeKernelWitness_eval hn hz

theorem parabolicH1_add_ellipticFixed_add_one_le_level_three {n : ℕ} (hn : 0 < n) :
    Module.finrank ℂ (ParabolicH1 3 n) +
      Module.finrank ℂ (levelThreeAction n - LinearMap.id).ker + 1 ≤ n := by
  have : FiniteDimensional ℂ (gammaOneRep 3 n) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 2) ℂ n)
  have hi : Function.Injective (normalizedToThreeNormKernel n) := by
    intro c d h
    exact normalizedEvalThreeElliptic_injective n (congrArg Subtype.val h)
  have hr : (normalizedToThreeNormKernel n).range < ⊤ :=
    lt_top_iff_ne_top.mpr (fun h => normalizedToThreeNormKernel_not_surjective hn
      (LinearMap.range_eq_top.mp h))
  have hd := Submodule.finrank_lt_finrank_of_lt hr
  rw [LinearMap.finrank_range_of_inj hi, finrank_top,
    normalizedParabolic_finrank (by decide : 0 < 3) hn] at hd
  have he := (levelThreeNorm n).finrank_range_add_finrank_ker
  have hrange : (levelThreeNorm n).range = (levelThreeAction n - LinearMap.id).ker :=
    LinearMap.range_cubic_norm_eq_ker_sub_id _ (levelThreeAction_cubic n)
  rw [hrange] at he
  change _ + _ = Module.finrank ℂ (Sym ℂ n) at he
  rw [finrank_sym] at he
  omega

end MTT.Cohomology

/-! # The odd-degree elliptic fixed-space count at level three -/

noncomputable section

open scoped MatrixGroups

namespace MTT.Cohomology

theorem fullSymRep_neg_of_odd {n : ℕ} (hn : Odd n) (g : SL(2, ℤ)) :
    (fullSymRep n).ρ (-g) = -(fullSymRep n).ρ g := by
  have hz : (fullSymRep n).ρ (-1) = -1 := by
    apply LinearMap.ext
    intro P
    apply Subtype.ext
    change act (-1) P.val = -P.val
    rw [act_neg_one_of_homogeneous P.property, hn.neg_one_pow, neg_one_smul]
  rw [← neg_one_mul g, map_mul, hz, neg_one_mul]

theorem trace_fullSymRep_conjugate (n : ℕ) (p g : SL(2, ℤ)) :
    LinearMap.trace ℂ (fullSymRep n) ((fullSymRep n).ρ (p * g * p⁻¹)) =
      LinearMap.trace ℂ (fullSymRep n) ((fullSymRep n).ρ g) := by
  rw [(fullSymRep n).ρ.map_mul, (fullSymRep n).ρ.map_mul, LinearMap.trace_mul_cycle,
    ← (fullSymRep n).ρ.map_mul, inv_mul_cancel, (fullSymRep n).ρ.map_one, one_mul]

theorem trace_levelThreeAction_of_odd {n : ℕ} (hn : Odd n) :
    LinearMap.trace ℂ (gammaOneRep 3 n) (levelThreeAction n) =
      -LinearMap.trace ℂ (gammaOneRep 1 n)
        ((gammaOneRep 1 n).ρ (levelOneIncl (ModularGroup.S * ModularGroup.T))) := by
  have hE : gammaOneThreeElliptic.val =
      (ModularGroup.S * ModularGroup.T⁻¹) * (-(ModularGroup.S * ModularGroup.T)) *
        (ModularGroup.S * ModularGroup.T⁻¹)⁻¹ := by decide
  change LinearMap.trace ℂ (fullSymRep n) ((fullSymRep n).ρ gammaOneThreeElliptic.val) = _
  rw [hE, trace_fullSymRep_conjugate, fullSymRep_neg_of_odd hn, map_neg]
  rfl

theorem trace_levelThreeAction_sq (n : ℕ) :
    LinearMap.trace ℂ (gammaOneRep 3 n) (levelThreeAction n ^ 2) =
      LinearMap.trace ℂ (gammaOneRep 1 n)
        (((gammaOneRep 1 n).ρ (levelOneIncl (ModularGroup.S * ModularGroup.T))) ^ 2) := by
  have hE : gammaOneThreeElliptic.val ^ 2 =
      (ModularGroup.S * ModularGroup.T⁻¹) * (ModularGroup.S * ModularGroup.T) ^ 2 *
        (ModularGroup.S * ModularGroup.T⁻¹)⁻¹ := by decide
  have hp := congrArg (LinearMap.trace ℂ (fullSymRep n))
    ((fullSymRep n).ρ.map_pow gammaOneThreeElliptic.val 2)
  calc
    _ = LinearMap.trace ℂ (fullSymRep n)
        ((fullSymRep n).ρ (gammaOneThreeElliptic.val ^ 2)) := hp.symm
    _ = LinearMap.trace ℂ (fullSymRep n)
        ((fullSymRep n).ρ ((ModularGroup.S * ModularGroup.T) ^ 2)) := by
      rw [hE, trace_fullSymRep_conjugate]
    _ = _ := congrArg (LinearMap.trace ℂ (fullSymRep n))
      ((fullSymRep n).ρ.map_pow (ModularGroup.S * ModularGroup.T) 2)

theorem binaryGeometricSum_sq_odd (a b : ℂ) (ha : a ^ 2 = -b) (hb : b ^ 2 = -a)
    {n : ℕ} (hn : Odd n) :
    (∑ j : Fin (n + 1), (a ^ j.val * b ^ (n - j.val)) ^ 2) =
      -(∑ j : Fin (n + 1), a ^ j.val * b ^ (n - j.val)) := by
  rw [binaryGeometricSum_comm a b, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hj : j.val + (n - j.val) = n := Nat.add_sub_of_le (by omega)
  calc
    _ = (a ^ 2) ^ j.val * (b ^ 2) ^ (n - j.val) := by
      rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm j.val,
        Nat.mul_comm (n - j.val), pow_mul, pow_mul]
    _ = (-b) ^ j.val * (-a) ^ (n - j.val) := by rw [ha, hb]
    _ = (-1 : ℂ) ^ n * (b ^ j.val * a ^ (n - j.val)) := by
      rw [neg_pow b j.val, neg_pow a (n - j.val)]
      have hs : (-1 : ℂ) ^ j.val * (-1 : ℂ) ^ (n - j.val) = (-1 : ℂ) ^ n := by
        rw [← pow_add, hj]
      calc
        _ = ((-1 : ℂ) ^ j.val * (-1 : ℂ) ^ (n - j.val)) *
            (b ^ j.val * a ^ (n - j.val)) := by ring
        _ = _ := by rw [hs]
    _ = _ := by rw [hn.neg_one_pow, neg_one_mul]

theorem trace_levelThreeAction_sq_eq {n : ℕ} (hn : Odd n) :
    LinearMap.trace ℂ (gammaOneRep 3 n) (levelThreeAction n ^ 2) =
      LinearMap.trace ℂ (gammaOneRep 3 n) (levelThreeAction n) := by
  obtain ⟨a, b, hab, ha, hb, hs⟩ := exists_elliptic_eigenvalues
  rw [trace_levelThreeAction_sq, trace_levelThreeAction_of_odd hn,
    trace_levelOneAction_ST_sq a b hab ha hb, trace_levelOneAction_ST a b hab ha hb]
  apply binaryGeometricSum_sq_odd a b _ _ hn
  · linear_combination ha + hs
  · linear_combination hb + hs

theorem binaryGeometricSum_odd (a b : ℂ) (hab : a ≠ b)
    (ha : a ^ 2 - a + 1 = 0) (hb : b ^ 2 - b + 1 = 0) (m : ℕ) :
    (∑ j : Fin (2 * m + 2), a ^ j.val * b ^ (2 * m + 1 - j.val)) =
      if m % 3 = 0 then 1 else if m % 3 = 1 then -1 else 0 := by
  have hpow (x : ℂ) (hx : x ^ 2 - x + 1 = 0) :
      x ^ (2 * m + 2) = x ^ (2 * (m % 3) + 2) := by
    have h3 : x ^ 3 = -1 := by linear_combination (x + 1) * hx
    have h6 : x ^ 6 = 1 := by rw [show 6 = 3 * 2 by decide, pow_mul, h3]; norm_num
    rw [show 2 * m + 2 = 6 * (m / 3) + (2 * (m % 3) + 2) by omega,
      pow_add, pow_mul, h6, one_pow, one_mul]
  have h3 (x : ℂ) (hx : x ^ 2 - x + 1 = 0) : x ^ 3 = -1 := by
    linear_combination (x + 1) * hx
  have h4 (x : ℂ) (hx : x ^ 2 - x + 1 = 0) : x ^ 4 = -x := by
    calc
      _ = x ^ 3 * x := by ring
      _ = -x := by rw [h3 x hx, neg_one_mul]
  have h6 (x : ℂ) (hx : x ^ 2 - x + 1 = 0) : x ^ 6 = 1 := by
    rw [show 6 = 3 * 2 by decide, pow_mul, h3 x hx]
    norm_num
  apply mul_right_cancel₀ (sub_ne_zero.mpr hab)
  rw [binaryGeometricSum_mul_sub, hpow a ha, hpow b hb]
  have hm : m % 3 < 3 := Nat.mod_lt _ (by decide)
  interval_cases hr : m % 3
  · norm_num
    linear_combination ha - hb
  · norm_num [h4 a ha, h4 b hb]
    ring
  · norm_num [h6 a ha, h6 b hb]

theorem trace_levelThreeAction_odd (m : ℕ) :
    LinearMap.trace ℂ (gammaOneRep 3 (2 * m + 1)) (levelThreeAction (2 * m + 1)) =
      if m % 3 = 0 then -1 else if m % 3 = 1 then 1 else 0 := by
  obtain ⟨a, b, hab, ha, hb, hs⟩ := exists_elliptic_eigenvalues
  have hn : Odd (2 * m + 1) := ⟨m, rfl⟩
  rw [trace_levelThreeAction_of_odd hn, trace_levelOneAction_ST a b hab ha hb,
    binaryGeometricSum_odd a b hab ha hb]
  split_ifs <;> norm_num

theorem finrank_levelThreeAction_fixed (m : ℕ) :
    Module.finrank ℂ (levelThreeAction (2 * m + 1) - LinearMap.id).ker =
      2 * ((m + 2) / 3) := by
  have : FiniteDimensional ℂ (gammaOneRep 3 (2 * m + 1)) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 2) ℂ (2 * m + 1))
  have hn : Odd (2 * m + 1) := ⟨m, rfl⟩
  have h := LinearMap.three_mul_finrank_fixed_eq_trace
    (levelThreeAction (2 * m + 1)) (levelThreeAction_cubic (2 * m + 1))
  rw [trace_levelThreeAction_sq_eq hn, trace_levelThreeAction_odd,
    show Module.finrank ℂ (gammaOneRep 3 (2 * m + 1)) = 2 * m + 2 from
      finrank_sym (2 * m + 1)] at h
  have hm : (m : ℂ) = 3 * (m / 3 : ℕ) + (m % 3 : ℕ) := by
    exact_mod_cast (Nat.mod_add_div m 3).symm.trans (by omega)
  have hlt : m % 3 < 3 := Nat.mod_lt _ (by decide)
  have hd : (Module.finrank ℂ (levelThreeAction (2 * m + 1) - LinearMap.id).ker : ℂ) =
      2 * ((m + 2) / 3 : ℕ) := by
    interval_cases hr : m % 3
    · have hq : (m + 2) / 3 = m / 3 := by omega
      rw [hq]
      norm_num [hr] at h hm
      linear_combination (norm := ring1!) h / 3 + (2 / 3 : ℂ) * hm
    · have hq : (m + 2) / 3 = m / 3 + 1 := by omega
      rw [hq]
      norm_num [hr] at h hm ⊢
      linear_combination (norm := ring1!) h / 3 + (2 / 3 : ℂ) * hm
    · have hq : (m + 2) / 3 = m / 3 + 1 := by omega
      rw [hq]
      norm_num [hr] at h hm ⊢
      linear_combination (norm := ring1!) h / 3 + (2 / 3 : ℂ) * hm
  exact_mod_cast hd

theorem parabolicH1_finrank_le_level_three_numeric {n : ℕ} (hn : 0 < n) (hno : Odd n) :
    Module.finrank ℂ (ParabolicH1 3 n) ≤ 2 * ((n + 2) / 3 - 1) := by
  obtain ⟨m, rfl⟩ := hno
  have hd := parabolicH1_add_ellipticFixed_add_one_le_level_three hn
  rw [finrank_levelThreeAction_fixed] at hd
  omega

end MTT.Cohomology

theorem solution {n : ℕ} (hn : 0 < n) (hno : Odd n) :
    Module.finrank ℂ (MTT.Cohomology.ParabolicH1 3 n) ≤ 2 * ((n + 2) / 3 - 1) :=
  MTT.Cohomology.parabolicH1_finrank_le_level_three_numeric hn hno
