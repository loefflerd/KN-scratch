module

public import Definitions.MTT.Def_MTT_ParabolicCohomology
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.LinearAlgebra.Trace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.RingTheory.RootsOfUnity.Complex
import Definitions.MTT.Def_MTT_LevelOnePeriodRelations

section privateSection

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
end

/-!
# Central negative action kills one-cocycles modulo coboundaries

This is the algebraic vanishing argument needed for odd symmetric powers at
levels one and two. It does not use the analytic period-injectivity theorem.
-/

noncomputable section

namespace groupCohomology

variable {G : Type} [Group G] (A : Rep ℂ G)

/-- If a central element acts by minus the identity, every cocycle is principal. -/
theorem cocycle_principal_of_central_neg (z : G) (hz : ∀ g, z * g = g * z)
    (hρ : ∀ v : A, A.ρ z v = -v) (c : cocycles₁ A) :
    ∃ P : A, ∀ g, c g = A.ρ g P - P := by
  refine ⟨(- (2 : ℂ)⁻¹) • c z, fun g => ?_⟩
  have hc := (mem_cocycles₁_iff c).mp c.property
  have heq : -c g + c z = A.ρ g (c z) + c g := by
    rw [← hρ, ← hc, hz, hc]
  have hact : A.ρ g (c z) = -c g + c z - c g := eq_sub_of_add_eq heq.symm
  rw [map_smul, hact]
  module

end groupCohomology

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

theorem neg_one_mem_Gamma1_of_le_two {N : ℕ} (hN : 0 < N) (hN₂ : N ≤ 2) :
    (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ CongruenceSubgroup.Gamma1 N := by
  rcases (show N = 1 ∨ N = 2 by omega) with rfl | rfl <;>
    norm_num [CongruenceSubgroup.Gamma1_mem, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply] <;> decide

theorem parabolicH1_subsingleton_of_odd_small_level {N n : ℕ}
    (hN : 0 < N) (hN₂ : N ≤ 2) (hn : Odd n) : Subsingleton (ParabolicH1 N n) := by
  let z : CongruenceSubgroup.Gamma1 N := ⟨-1, neg_one_mem_Gamma1_of_le_two hN hN₂⟩
  have hz (g : CongruenceSubgroup.Gamma1 N) : z * g = g * z := by
    apply Subtype.ext
    change (-1) * g.val = g.val * (-1)
    simp only [neg_mul, one_mul, mul_neg, mul_one]
  have hρ (P : gammaOneRep N n) : (gammaOneRep N n).ρ z P = -P := by
    apply Subtype.ext
    change act (-1) P.val = -P.val
    rw [act_neg_one_of_homogeneous P.property, hn.neg_one_pow, neg_one_smul]
  have htop : parabolicCoboundaries N n = ⊤ := by
    apply top_unique
    intro c _
    apply (mem_parabolicCoboundaries_iff c).mpr
    exact groupCohomology.cocycle_principal_of_central_neg (gammaOneRep N n) z hz hρ
      ⟨c.val, c.property.1⟩
  change Subsingleton (parabolicCocycles N n ⧸ parabolicCoboundaries N n)
  rw [htop]
  infer_instance

end MTT.Cohomology
end

/-!
# Translation-normalized parabolic cocycles

Every parabolic cohomology class has a representative vanishing at the
translation T. This is obtained by subtracting its explicit principal witness
at infinity, and is valid at every level and symmetric-power degree.
-/

noncomputable section

namespace MTT.Cohomology

open groupCohomology

/-- The standard translation belongs to every Gamma1(N). -/
def gammaOneT (N : ℕ) : CongruenceSubgroup.Gamma1 N :=
  ⟨ModularGroup.T, by
    rw [CongruenceSubgroup.Gamma1_mem]
    norm_num [ModularGroup.T]⟩

theorem gammaOneT_fixes_infty (N : ℕ) :
    cuspAct (gammaOneT N).val OnePoint.infty = OnePoint.infty :=
  OnePoint.smul_infty_eq_self_iff.mpr rfl

/-- The principal cocycle attached to a coefficient vector. -/
def principalParabolic (N n : ℕ) (P : gammaOneRep N n) : parabolicCocycles N n :=
  ⟨d₀₁ (gammaOneRep N n) P,
    coboundaries_le_parabolicCocycles N n ⟨P, rfl⟩⟩

theorem principalParabolic_mem (N n : ℕ) (P : gammaOneRep N n) :
    principalParabolic N n P ∈ parabolicCoboundaries N n :=
  (mem_parabolicCoboundaries_iff _).mpr ⟨P, fun _ => rfl⟩

/-- Normalized parabolic cocycles vanish on the standard translation. -/
def normalizedParabolic (N n : ℕ) : Submodule ℂ (parabolicCocycles N n) :=
  LinearMap.ker ((LinearMap.proj (gammaOneT N)).comp (parabolicCocycles N n).subtype)

theorem exists_normalizedParabolic {N n : ℕ} (c : parabolicCocycles N n) :
    ∃ P : gammaOneRep N n, c - principalParabolic N n P ∈ normalizedParabolic N n := by
  obtain ⟨P, hP⟩ := ((mem_parabolicCocycles_iff _).mp c.property).2 OnePoint.infty
    (gammaOneT N) (gammaOneT_fixes_infty N)
  refine ⟨P, ?_⟩
  change c.val (gammaOneT N) - ((gammaOneRep N n).ρ (gammaOneT N) P - P) = 0
  exact sub_eq_zero.mpr hP

/-- Passing to cohomology from translation-normalized representatives. -/
def normalizedToH1 (N n : ℕ) : normalizedParabolic N n →ₗ[ℂ] ParabolicH1 N n :=
  (parabolicCoboundaries N n).mkQ.comp (normalizedParabolic N n).subtype

theorem normalizedToH1_surjective (N n : ℕ) : Function.Surjective (normalizedToH1 N n) := by
  intro q
  obtain ⟨c, rfl⟩ := (parabolicCoboundaries N n).mkQ_surjective q
  obtain ⟨P, hP⟩ := exists_normalizedParabolic c
  refine ⟨⟨c - principalParabolic N n P, hP⟩, ?_⟩
  change (parabolicCoboundaries N n).mkQ (c - principalParabolic N n P) = _
  rw [map_sub]
  have hz : (parabolicCoboundaries N n).mkQ (principalParabolic N n P) = 0 := by
    apply (LinearMap.mem_ker).mp
    rw [Submodule.ker_mkQ]
    exact principalParabolic_mem N n P
  rw [hz, sub_zero]

end MTT.Cohomology
end

/-!
# A normalized level-one cocycle is determined by its value at S

The translation-normalized model reduces the cohomology dimension question
to a subquotient of the symmetric-power coefficient space. The next step is
to impose the S and ST period-polynomial relations on this value.
-/

noncomputable section

namespace MTT.Cohomology

/-- The value at S of a translation-normalized level-one cocycle. -/
def normalizedEvalS (n : ℕ) : normalizedParabolic 1 n →ₗ[ℂ] gammaOneRep 1 n :=
  (LinearMap.proj (levelOneIncl ModularGroup.S)).comp
    ((parabolicCocycles 1 n).subtype.comp (normalizedParabolic 1 n).subtype)

theorem normalized_eq_zero_of_evalS_eq_zero {n : ℕ} (c : normalizedParabolic 1 n)
    (hS : normalizedEvalS n c = 0) : c = 0 := by
  have hc (g h : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
      c.val.val (levelOneIncl (g * h)) =
        (gammaOneRep 1 n).ρ (levelOneIncl g) (c.val.val (levelOneIncl h)) +
          c.val.val (levelOneIncl g) := by
    rw [map_mul]
    exact ((mem_parabolicCocycles_iff _).mp c.val.property).1 _ _
  have h0 : c.val.val (levelOneIncl 1) = 0 :=
    groupCohomology.cocycles₁_map_one ⟨c.val.val, c.val.property.1⟩
  have hT : c.val.val (levelOneIncl ModularGroup.T) = 0 := c.property
  have hall (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
      c.val.val (levelOneIncl g) = 0 := by
    have hg : g ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} :=
      SpecialLinearGroup.SL2Z_generators.symm ▸ Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem g hg => rcases hg with rfl | rfl; exact hS; exact hT
    | one => exact h0
    | mul g h _ _ hg hh => rw [hc, hg, hh, map_zero, add_zero]
    | inv g _ hg =>
        have heq := hc g⁻¹ g
        simpa only [inv_mul_cancel, h0, hg, map_zero, zero_add] using heq.symm
  apply Subtype.ext
  apply Subtype.ext
  funext g
  exact hall g.val

theorem normalizedEvalS_injective (n : ℕ) : Function.Injective (normalizedEvalS n) := by
  intro c d h
  apply sub_eq_zero.mp
  apply normalized_eq_zero_of_evalS_eq_zero
  rw [map_sub, h, sub_self]

theorem levelOne_cocycle_neg_one_eq_zero {n : ℕ} (hn : Even n)
    (c : parabolicCocycles 1 n) : c.val (levelOneIncl (-1)) = 0 := by
  have hρ (P : gammaOneRep 1 n) : (gammaOneRep 1 n).ρ (levelOneIncl (-1)) P = P := by
    apply Subtype.ext
    change act (-1) P.val = P.val
    rw [act_neg_one_of_homogeneous P.property, hn.neg_one_pow, one_smul]
  have hc := ((mem_parabolicCocycles_iff _).mp c.property).1
    (levelOneIncl (-1)) (levelOneIncl (-1))
  have hz : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) * (-1) = 1 := by decide
  have h0 : c.val 1 = 0 := groupCohomology.cocycles₁_map_one ⟨c.val, c.property.1⟩
  rw [← map_mul, hz, map_one, h0, hρ] at hc
  have hscale : (2 : ℂ) • c.val (levelOneIncl (-1)) = 0 := by
    simpa only [two_smul, one_smul] using hc.symm
  exact (smul_eq_zero.mp hscale).resolve_left (by norm_num)

theorem normalizedEvalS_two_term {n : ℕ} (hn : Even n)
    (c : normalizedParabolic 1 n) :
    (gammaOneRep 1 n).ρ (levelOneIncl ModularGroup.S) (normalizedEvalS n c) +
      normalizedEvalS n c = 0 := by
  have hc := ((mem_parabolicCocycles_iff _).mp c.val.property).1
    (levelOneIncl ModularGroup.S) (levelOneIncl ModularGroup.S)
  have hS₂ : ModularGroup.S * ModularGroup.S = -1 := by decide
  rw [← map_mul, hS₂, levelOne_cocycle_neg_one_eq_zero hn] at hc
  exact hc.symm

theorem normalizedEvalS_three_term {n : ℕ} (hn : Even n)
    (c : normalizedParabolic 1 n) :
    (gammaOneRep 1 n).ρ (levelOneIncl (ModularGroup.S * ModularGroup.T))
        ((gammaOneRep 1 n).ρ (levelOneIncl (ModularGroup.S * ModularGroup.T))
          (normalizedEvalS n c)) +
      (gammaOneRep 1 n).ρ (levelOneIncl (ModularGroup.S * ModularGroup.T))
        (normalizedEvalS n c) + normalizedEvalS n c = 0 := by
  let r := levelOneIncl (ModularGroup.S * ModularGroup.T)
  have hc := ((mem_parabolicCocycles_iff _).mp c.val.property).1
  have hT : c.val.val (levelOneIncl ModularGroup.T) = 0 := c.property
  have hr : c.val.val r = normalizedEvalS n c := by
    dsimp [r]
    rw [map_mul, hc, hT, map_zero, zero_add]
    rfl
  have hR₃ : r * (r * r) = levelOneIncl (-1) := by
    simp only [r, ← map_mul]
    congr 1
    decide
  have heq := congrArg c.val.val hR₃
  rw [hc, hc, hr, map_add, levelOne_cocycle_neg_one_eq_zero hn] at heq
  exact heq

def normalizedToRelations {n : ℕ} (hn : Even n) :
    normalizedParabolic 1 n →ₗ[ℂ] periodRelations n :=
  (normalizedEvalS n).codRestrict _ fun c => (mem_periodRelations_iff _).mpr
    ⟨normalizedEvalS_two_term hn c, normalizedEvalS_three_term hn c⟩

theorem normalizedToRelations_injective {n : ℕ} (hn : Even n) :
    Function.Injective (normalizedToRelations hn) := by
  intro c d h
  apply normalizedEvalS_injective n
  exact congrArg Subtype.val h

end MTT.Cohomology
end

/-!
# Bounding parabolic cohomology by period relations

Normalization surjects onto cohomology and evaluation at S injects into the
period-relation space. For positive degree, the principal cocycle of X^n is
a nonzero normalized cocycle in the kernel, accounting for one dimension.
-/

noncomputable section

namespace LinearMap

theorem finrank_add_one_le_of_surjective_of_injective {K V W U : Type*}
    [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup U] [Module K U] [FiniteDimensional K V] [FiniteDimensional K U]
    (f : V →ₗ[K] W) (g : V →ₗ[K] U) (hf : Function.Surjective f)
    (hg : Function.Injective g) (hker : f.ker ≠ ⊥) :
    Module.finrank K W + 1 ≤ Module.finrank K U := by
  have hdimker : 1 ≤ Module.finrank K f.ker := Submodule.one_le_finrank_iff.mpr hker
  have hrank := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hf, finrank_top] at hrank
  have hle := LinearMap.finrank_le_finrank_of_injective (f := g) hg
  omega

end LinearMap

namespace MTT.Cohomology

open MvPolynomial

def xPower (n : ℕ) : gammaOneRep 1 n := ⟨X 0 ^ n, isHomogeneous_X_pow 0 n⟩

theorem xPower_T_invariant (n : ℕ) : (gammaOneRep 1 n).ρ (gammaOneT 1) (xPower n) =
    xPower n := by
  apply Subtype.ext
  change act ModularGroup.T.val (X 0 ^ n : Binary ℂ) = X 0 ^ n
  change MvPolynomial.aeval _ (X 0 ^ n : Binary ℂ) = _
  simp [ModularGroup.T, Fin.sum_univ_two]

def xPowerCoboundary (n : ℕ) : normalizedParabolic 1 n :=
  ⟨principalParabolic 1 n (xPower n), by
    change (gammaOneRep 1 n).ρ (gammaOneT 1) (xPower n) - xPower n = 0
    rw [xPower_T_invariant, sub_self]⟩

theorem xPowerCoboundary_mem_ker (n : ℕ) :
    xPowerCoboundary n ∈ LinearMap.ker (normalizedToH1 1 n) := by
  change (parabolicCoboundaries 1 n).mkQ (principalParabolic 1 n (xPower n)) = 0
  apply (LinearMap.mem_ker).mp
  rw [Submodule.ker_mkQ]
  exact principalParabolic_mem 1 n (xPower n)

theorem xPowerCoboundary_ne_zero {n : ℕ} (hn : 0 < n) : xPowerCoboundary n ≠ 0 := by
  intro h
  have heq := congrArg (fun c => (normalizedEvalS n c).val) h
  change act ModularGroup.S.val (X 0 ^ n : Binary ℂ) - X 0 ^ n = 0 at heq
  have hact : act ModularGroup.S.val (X 0 ^ n : Binary ℂ) = X 1 ^ n := by
    change MvPolynomial.aeval _ (X 0 ^ n : Binary ℂ) = _
    simp [ModularGroup.S, Fin.sum_univ_two]
  rw [hact] at heq
  have hev := congrArg (MvPolynomial.eval ![(1 : ℂ), 0]) heq
  simp [Nat.ne_of_gt hn] at hev

theorem finiteDimensional_normalizedParabolic_levelOne (n : ℕ) :
    FiniteDimensional ℂ (normalizedParabolic 1 n) := by
  have : FiniteDimensional ℂ (gammaOneRep 1 n) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 2) ℂ n)
  exact FiniteDimensional.of_injective (normalizedEvalS n) (normalizedEvalS_injective n)

theorem normalizedToH1_ker_ne_bot {n : ℕ} (hn : 0 < n) :
    LinearMap.ker (normalizedToH1 1 n) ≠ ⊥ := by
  intro h
  have hz := xPowerCoboundary_mem_ker n
  rw [h, Submodule.mem_bot] at hz
  exact xPowerCoboundary_ne_zero hn hz

theorem parabolicH1_add_one_le_periodRelations {n : ℕ} (hn : Even n) (hnpos : 0 < n) :
    Module.finrank ℂ (ParabolicH1 1 n) + 1 ≤ Module.finrank ℂ (periodRelations n) := by
  have := finiteDimensional_normalizedParabolic_levelOne n
  have : FiniteDimensional ℂ (gammaOneRep 1 n) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 2) ℂ n)
  exact LinearMap.finrank_add_one_le_of_surjective_of_injective
    (K := ℂ) (V := normalizedParabolic 1 n) (W := ParabolicH1 1 n) (U := periodRelations n)
    (normalizedToH1 1 n) (normalizedToRelations (n := n) hn) (normalizedToH1_surjective 1 n)
    (normalizedToRelations_injective (n := n) hn) (normalizedToH1_ker_ne_bot (n := n) hnpos)

end MTT.Cohomology
end

noncomputable section
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

theorem eval_symmetricPower_expansion {n : ℕ} (P : Sym ℂ n) (u v : ℂ) :
    eval ![u, v] P.val = ∑ j : Fin (n + 1), symmetricPowerCoordinates ℂ n P j *
      (u ^ j.val * v ^ (n - j.val)) := by
  conv_lhs => rw [symmetricPower_expansion P]
  simp

end MTT.Cohomology
end

/-!
# Translation invariants in the MTT symmetric power

Adapted from `invariant_eq_smul_X_pow` in the accepted MTT boundary-Hecke
proof 2c3fe658-d2de-4575-89b3-ebdfcfd22e7e. The argument is specialized to T
and uses the present coefficient basis; the source worker's files are untouched.
-/

noncomputable section

namespace MTT.Cohomology

theorem eval_scale_symmetricPower {n : ℕ} (P : Sym ℂ n) (c u v : ℂ) :
    MvPolynomial.eval ![c * u, c * v] P.val =
      c ^ n * MvPolynomial.eval ![u, v] P.val := by
  simp only [eval_symmetricPower_expansion P, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hj : j.val + (n - j.val) = n := by omega
  have hc : c ^ n = c ^ j.val * c ^ (n - j.val) := by rw [← pow_add, hj]
  rw [mul_pow, mul_pow, hc]
  ring

def dehomogenizeAtX (P : Binary ℂ) : Polynomial ℂ :=
  MvPolynomial.aeval (![Polynomial.C 1, Polynomial.X] : Fin 2 → Polynomial ℂ) P

theorem eval_dehomogenizeAtX (P : Binary ℂ) (t : ℂ) :
    Polynomial.eval t (dehomogenizeAtX P) = MvPolynomial.eval ![1, t] P := by
  unfold dehomogenizeAtX
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, Polynomial.eval_add, hp, hq, MvPolynomial.eval_add]
  | mul_X p i hp =>
    rw [map_mul, MvPolynomial.aeval_X, Polynomial.eval_mul, hp, MvPolynomial.eval_mul,
      MvPolynomial.eval_X]
    congr 1
    fin_cases i <;> simp

private theorem dehomogenizeAtX_eq_const_of_T_invariant {n : ℕ} (P : Sym ℂ n)
    (hP : act ModularGroup.T.val P.val = P.val) :
    dehomogenizeAtX P.val = Polynomial.C (MvPolynomial.eval ![1, 0] P.val) := by
  have hper (t : ℂ) : MvPolynomial.eval ![1, t + 1] P.val =
      MvPolynomial.eval ![1, t] P.val := by
    have h := congrArg (MvPolynomial.eval ![1, t]) hP
    simpa [eval_act, ModularGroup.T, add_comm] using h
  have hval (k : ℕ) : Polynomial.eval (k : ℂ) (dehomogenizeAtX P.val) =
      MvPolynomial.eval ![1, 0] P.val := by
    induction k with
    | zero => simp [eval_dehomogenizeAtX]
    | succ k ih =>
      simpa [eval_dehomogenizeAtX] using (hper k).trans (by
        simpa [eval_dehomogenizeAtX] using ih)
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (k : ℂ))
    Nat.cast_injective ?_
  intro k
  simpa only [Set.mem_ofPred_eq, Polynomial.eval_C] using hval k

theorem T_invariant_eq_smul_xPower {n : ℕ} (P : Sym ℂ n)
    (hP : act ModularGroup.T.val P.val = P.val) :
    P.val = MvPolynomial.eval ![1, 0] P.val • MvPolynomial.X 0 ^ n := by
  let c := MvPolynomial.eval ![1, 0] P.val
  have hc := dehomogenizeAtX_eq_const_of_T_invariant P hP
  have hval (u v : ℂ) : MvPolynomial.eval ![u, v]
      (MvPolynomial.X 0 * (P.val - MvPolynomial.C c * MvPolynomial.X 0 ^ n)) = 0 := by
    by_cases hu : u = 0
    · simp [hu]
    · have hPval : MvPolynomial.eval ![u, v] P.val = u ^ n * c := by
        have h := eval_scale_symmetricPower P u 1 (v / u)
        rw [mul_one, mul_div_cancel₀ _ hu] at h
        rw [h, ← eval_dehomogenizeAtX, hc, Polynomial.eval_C]
      simp only [MvPolynomial.eval_mul, MvPolynomial.eval_sub, MvPolynomial.eval_C,
        MvPolynomial.eval_pow, MvPolynomial.eval_X, hPval, Matrix.cons_val_zero]
      ring
  have hz : MvPolynomial.X 0 * (P.val - MvPolynomial.C c * MvPolynomial.X 0 ^ n) = 0 := by
    apply MvPolynomial.funext
    intro v
    have h := hval (v 0) (v 1)
    rwa [show ![v 0, v 1] = v by ext i; fin_cases i <;> rfl] at h
  have hz' := (mul_eq_zero.mp hz).resolve_left (MvPolynomial.X_ne_zero 0)
  simpa only [sub_eq_zero, MvPolynomial.smul_eq_C_mul] using hz'

end MTT.Cohomology
end

/-! # Generator differences span the positive-degree coefficient module -/

noncomputable section

namespace MTT.Cohomology

local instance (n : ℕ) : FiniteDimensional ℂ (gammaOneRep 1 n) :=
  Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 2) ℂ n)

def generatorDifference (n : ℕ) (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    Module.End ℂ (gammaOneRep 1 n) :=
  (gammaOneRep 1 n).ρ (levelOneIncl g) - LinearMap.id

theorem generatorDifference_apply (n : ℕ) (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (P : gammaOneRep 1 n) : generatorDifference n g P =
      (gammaOneRep 1 n).ρ (levelOneIncl g) P - P := rfl

theorem xPower_ne_zero (n : ℕ) : xPower n ≠ 0 := by
  intro h
  exact pow_ne_zero n (MvPolynomial.X_ne_zero (0 : Fin 2)) (congrArg Subtype.val h)

theorem ker_translationDifference (n : ℕ) :
    (generatorDifference n ModularGroup.T).ker = Submodule.span ℂ {xPower n} := by
  ext P
  rw [LinearMap.mem_ker, generatorDifference_apply, sub_eq_zero, Submodule.mem_span_singleton]
  constructor
  · intro h
    refine ⟨MvPolynomial.eval ![1, 0] P.val, ?_⟩
    apply Subtype.ext
    exact (T_invariant_eq_smul_xPower P (congrArg Subtype.val h)).symm
  · rintro ⟨a, rfl⟩
    rw [map_smul]
    exact congrArg (a • ·) (xPower_T_invariant n)

theorem finrank_translationDifference_range (n : ℕ) :
    Module.finrank ℂ (generatorDifference n ModularGroup.T).range = n := by
  have h := (generatorDifference n ModularGroup.T).finrank_range_add_finrank_ker
  rw [ker_translationDifference, finrank_span_singleton (xPower_ne_zero n)] at h
  change Module.finrank ℂ (generatorDifference n ModularGroup.T).range + 1 =
    Module.finrank ℂ (Sym ℂ n) at h
  rw [finrank_sym] at h
  omega

theorem eval_y_translationDifference (n : ℕ) (P : gammaOneRep 1 n) :
    MvPolynomial.eval ![0, 1] (generatorDifference n ModularGroup.T P).val = 0 := by
  change MvPolynomial.eval ![0, 1] (act ModularGroup.T.val P.val - P.val) = 0
  simp [MvPolynomial.eval_sub, eval_act, ModularGroup.T]

theorem inversionDifference_xPower_notMem_translationRange {n : ℕ} (hn : 0 < n) :
    generatorDifference n ModularGroup.S (xPower n) ∉
      (generatorDifference n ModularGroup.T).range := by
  rintro ⟨P, hP⟩
  have h := eval_y_translationDifference n P
  rw [hP] at h
  change MvPolynomial.eval ![0, 1]
    (act ModularGroup.S.val (MvPolynomial.X 0 ^ n) - MvPolynomial.X 0 ^ n) = 0 at h
  simp [MvPolynomial.eval_sub, eval_act, ModularGroup.S, Nat.ne_of_gt hn] at h

theorem translationRange_sup_inversionSpan {n : ℕ} (hn : 0 < n) :
    (generatorDifference n ModularGroup.T).range ⊔
      Submodule.span ℂ {generatorDifference n ModularGroup.S (xPower n)} = ⊤ := by
  apply Submodule.eq_top_iff_finrank_eq.mpr
  rw [Submodule.finrank_sup_span_singleton
    (inversionDifference_xPower_notMem_translationRange hn), finrank_translationDifference_range]
  exact (finrank_sym n).symm

theorem translationDifference_mem_generatorRanges (n : ℕ) (P : gammaOneRep 1 n) :
    generatorDifference n ModularGroup.T P ∈
      (generatorDifference n ModularGroup.S).range ⊔
        (generatorDifference n (ModularGroup.S * ModularGroup.T)).range := by
  have h : generatorDifference n ModularGroup.T P =
      generatorDifference n (ModularGroup.S * ModularGroup.T) P -
        generatorDifference n ModularGroup.S ((gammaOneRep 1 n).ρ
          (levelOneIncl ModularGroup.T) P) := by
    simp only [generatorDifference_apply, map_mul, Module.End.mul_apply]
    module
  rw [h]
  exact Submodule.sub_mem _ (Submodule.mem_sup_right ⟨P, rfl⟩)
    (Submodule.mem_sup_left ⟨_, rfl⟩)

theorem generatorDifference_ranges_sup_eq_top {n : ℕ} (hn : 0 < n) :
    (generatorDifference n ModularGroup.S).range ⊔
      (generatorDifference n (ModularGroup.S * ModularGroup.T)).range = ⊤ := by
  apply top_unique
  rw [← translationRange_sup_inversionSpan hn]
  apply sup_le
  · rintro P ⟨Q, rfl⟩
    exact translationDifference_mem_generatorRanges n Q
  · apply Submodule.span_le.mpr
    rintro P (rfl : P = generatorDifference n ModularGroup.S (xPower n))
    exact Submodule.mem_sup_left ⟨xPower n, rfl⟩

end MTT.Cohomology
end

/-! # Dimension of the period-relation space from the two fixed spaces -/

noncomputable section

namespace LinearMap

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

theorem range_add_id_eq_ker_sub_id (s : V →ₗ[K] V) (hs : Function.Involutive s) :
    (s + LinearMap.id).range = (s - LinearMap.id).ker := by
  ext P
  rw [mem_ker, sub_apply, id_apply, sub_eq_zero]
  constructor
  · rintro ⟨Q, rfl⟩
    change s (s Q + Q) = s Q + Q
    rw [map_add, hs Q]
    exact add_comm _ _
  · intro h
    refine ⟨(2 : K)⁻¹ • P, ?_⟩
    simp only [add_apply, id_apply, map_smul, h]
    module

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

omit [CharZero K] in
theorem finrank_inf_ker_add_ranges [FiniteDimensional K V] (s r : V →ₗ[K] V)
    (h : s.ker ⊔ r.ker = ⊤) :
    Module.finrank K ↥(s.ker ⊓ r.ker) + Module.finrank K s.range +
      Module.finrank K r.range = Module.finrank K V := by
  have hi := s.ker.finrank_sup_add_finrank_inf_eq r.ker
  rw [h, finrank_top] at hi
  have hs := s.finrank_range_add_finrank_ker
  have hr := r.finrank_range_add_finrank_ker
  omega

end LinearMap

namespace MTT.Cohomology

local instance (n : ℕ) : FiniteDimensional ℂ (gammaOneRep 1 n) :=
  Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 2) ℂ n)

theorem levelOneAction_pow_neg_one {n m : ℕ} (hn : Even n)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hg : g ^ m = -1) :
    ((gammaOneRep 1 n).ρ (levelOneIncl g)) ^ m = LinearMap.id := by
  rw [← map_pow, ← map_pow, hg]
  ext P
  apply Subtype.ext
  change act (-1) P.val = P.val
  rw [act_neg_one_of_homogeneous P.property, hn.neg_one_pow, one_smul]

theorem levelOneAction_S_involutive {n : ℕ} (hn : Even n) :
    Function.Involutive ((gammaOneRep 1 n).ρ (levelOneIncl ModularGroup.S)) := by
  intro P
  have h := levelOneAction_pow_neg_one (m := 2) hn ModularGroup.S (by decide)
  exact congrArg (fun f : Module.End ℂ (gammaOneRep 1 n) => f P) h

theorem levelOneAction_ST_cubic {n : ℕ} (hn : Even n) (P : gammaOneRep 1 n) :
    (gammaOneRep 1 n).ρ (levelOneIncl (ModularGroup.S * ModularGroup.T))
      ((gammaOneRep 1 n).ρ (levelOneIncl (ModularGroup.S * ModularGroup.T))
        ((gammaOneRep 1 n).ρ (levelOneIncl (ModularGroup.S * ModularGroup.T)) P)) = P := by
  have h := levelOneAction_pow_neg_one (m := 3) hn (ModularGroup.S * ModularGroup.T) (by decide)
  exact congrArg (fun f : Module.End ℂ (gammaOneRep 1 n) => f P) h

theorem periodRelation_norm_kernels_sup_eq_top {n : ℕ} (hn : Even n) (hnpos : 0 < n) :
    ((gammaOneRep 1 n).ρ (levelOneIncl ModularGroup.S) + LinearMap.id).ker ⊔
      (((gammaOneRep 1 n).ρ (levelOneIncl (ModularGroup.S * ModularGroup.T))) ^ 2 +
        (gammaOneRep 1 n).ρ (levelOneIncl (ModularGroup.S * ModularGroup.T)) +
          LinearMap.id).ker = ⊤ := by
  apply top_unique
  rw [← generatorDifference_ranges_sup_eq_top hnpos]
  apply sup_le_sup
  · rintro P ⟨Q, rfl⟩
    change (gammaOneRep 1 n).ρ (levelOneIncl ModularGroup.S)
      ((gammaOneRep 1 n).ρ (levelOneIncl ModularGroup.S) Q - Q) +
        ((gammaOneRep 1 n).ρ (levelOneIncl ModularGroup.S) Q - Q) = 0
    rw [map_sub, levelOneAction_S_involutive hn Q]
    module
  · rintro P ⟨Q, rfl⟩
    change (gammaOneRep 1 n).ρ (levelOneIncl (ModularGroup.S * ModularGroup.T))
      ((gammaOneRep 1 n).ρ (levelOneIncl (ModularGroup.S * ModularGroup.T))
        ((gammaOneRep 1 n).ρ (levelOneIncl (ModularGroup.S * ModularGroup.T)) Q - Q)) +
      (gammaOneRep 1 n).ρ (levelOneIncl (ModularGroup.S * ModularGroup.T))
        ((gammaOneRep 1 n).ρ (levelOneIncl (ModularGroup.S * ModularGroup.T)) Q - Q) +
      ((gammaOneRep 1 n).ρ (levelOneIncl (ModularGroup.S * ModularGroup.T)) Q - Q) = 0
    simp only [map_sub, levelOneAction_ST_cubic hn Q]
    module

theorem periodRelations_finrank_add_fixed_finranks {n : ℕ} (hn : Even n) (hnpos : 0 < n) :
    Module.finrank ℂ (periodRelations n) +
      Module.finrank ℂ (generatorDifference n ModularGroup.S).ker +
      Module.finrank ℂ (generatorDifference n (ModularGroup.S * ModularGroup.T)).ker = n + 1 := by
  have h := LinearMap.finrank_inf_ker_add_ranges
    ((gammaOneRep 1 n).ρ (levelOneIncl ModularGroup.S) + LinearMap.id)
    (((gammaOneRep 1 n).ρ (levelOneIncl (ModularGroup.S * ModularGroup.T))) ^ 2 +
      (gammaOneRep 1 n).ρ (levelOneIncl (ModularGroup.S * ModularGroup.T)) + LinearMap.id)
    (periodRelation_norm_kernels_sup_eq_top hn hnpos)
  rw [LinearMap.range_add_id_eq_ker_sub_id _ (levelOneAction_S_involutive hn),
    LinearMap.range_cubic_norm_eq_ker_sub_id _ (levelOneAction_ST_cubic hn)] at h
  exact h.trans (finrank_sym n)

end MTT.Cohomology
end

/-! # The inversion fixed-space dimension -/

noncomputable section

namespace LinearMap

theorem two_mul_finrank_fixed_eq_trace {K V : Type*} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (s : Module.End K V) (hs : Function.Involutive s) :
    (2 : K) * Module.finrank K (s - LinearMap.id).ker =
      Module.finrank K V + LinearMap.trace K V s := by
  have hp : LinearMap.IsProj (s - LinearMap.id).ker ((2 : K)⁻¹ • (s + LinearMap.id)) := by
    constructor
    · intro P
      change s ((2 : K)⁻¹ • (s P + P)) - (2 : K)⁻¹ • (s P + P) = 0
      rw [map_smul, map_add, hs P]
      module
    · intro P hP
      have h : s P = P := sub_eq_zero.mp hP
      change (2 : K)⁻¹ • (s P + P) = P
      rw [h]
      module
  have ht := hp.trace
  rw [map_smul, map_add, LinearMap.trace_id, smul_eq_mul] at ht
  linear_combination -2 * ht

end LinearMap

namespace MTT.Cohomology

theorem levelOneAction_S_basis {n : ℕ} (j : Fin (n + 1)) :
    (gammaOneRep 1 n).ρ (levelOneIncl ModularGroup.S) (symmetricPowerBasis ℂ n j) =
      (-1 : ℂ) ^ (n - j.val) • symmetricPowerBasis ℂ n j.rev := by
  apply Subtype.ext
  change act ModularGroup.S.val (symmetricPowerBasis ℂ n j).val =
    (-1 : ℂ) ^ (n - j.val) • (symmetricPowerBasis ℂ n j.rev).val
  rw [symmetricPowerBasis_val_eq, symmetricPowerBasis_val_eq]
  have hj : n - (n - j.val) = j.val := Nat.sub_sub_self (by omega)
  have hp := neg_pow (MvPolynomial.X 0 : Binary ℂ) (n - j.val)
  simp [act, ModularGroup.S, Fin.sum_univ_two, Fin.rev, hj,
    Algebra.smul_def, hp, mul_comm, mul_left_comm, mul_assoc]

theorem trace_levelOneAction_S (m : ℕ) :
    LinearMap.trace ℂ (gammaOneRep 1 (2 * m))
      ((gammaOneRep 1 (2 * m)).ρ (levelOneIncl ModularGroup.S)) = (-1 : ℂ) ^ m := by
  classical
  let b : Module.Basis (Fin (2 * m + 1)) ℂ (gammaOneRep 1 (2 * m)) :=
    symmetricPowerBasis ℂ (2 * m)
  have hb (j : Fin (2 * m + 1)) :
      (gammaOneRep 1 (2 * m)).ρ (levelOneIncl ModularGroup.S) (b j) =
        (-1 : ℂ) ^ (2 * m - j.val) • b j.rev := levelOneAction_S_basis j
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, hb, map_smul,
    Module.Basis.repr_self_apply, Finsupp.smul_apply, smul_eq_mul]
  let mid : Fin (2 * m + 1) := ⟨m, by omega⟩
  rw [Finset.sum_eq_single mid]
  · have hm : mid.rev = mid := by apply Fin.ext; simp [mid, Fin.rev]; omega
    simp [hm, mid, show 2 * m - m = m by omega]
  · intro j _ hj
    have hne : j.rev ≠ j := by
      intro h
      have hv := congrArg Fin.val h
      have hjv : j.val < 2 * m + 1 := j.isLt
      apply hj
      apply Fin.ext
      dsimp [mid]
      simp [Fin.rev] at hv
      omega
    simp [hne]
  · simp

theorem finrank_inversionFixed (m : ℕ) :
    Module.finrank ℂ (generatorDifference (2 * m) ModularGroup.S).ker =
      m + if Even m then 1 else 0 := by
  have : FiniteDimensional ℂ (gammaOneRep 1 (2 * m)) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 2) ℂ (2 * m))
  have h := LinearMap.two_mul_finrank_fixed_eq_trace
    (V := gammaOneRep 1 (2 * m))
    ((gammaOneRep 1 (2 * m)).ρ (levelOneIncl ModularGroup.S))
    (levelOneAction_S_involutive (show Even (2 * m) from ⟨m, by omega⟩))
  rw [trace_levelOneAction_S, show Module.finrank ℂ (gammaOneRep 1 (2 * m)) = 2 * m + 1
    from finrank_sym (2 * m)] at h
  by_cases hm : Even m
  · rw [ite_eq_left hm]
    rw [hm.neg_one_pow] at h
    push_cast at h
    have hc : (Module.finrank ℂ (generatorDifference (2 * m) ModularGroup.S).ker : ℂ) =
        (m : ℂ) + 1 := by
      dsimp only [generatorDifference]
      linear_combination (norm := ring1!) h / 2
    exact_mod_cast hc
  · rw [ite_eq_right hm, add_zero]
    rw [(Nat.not_even_iff_odd.mp hm).neg_one_pow] at h
    push_cast at h
    have hc : (Module.finrank ℂ (generatorDifference (2 * m) ModularGroup.S).ker : ℂ) =
        (m : ℂ) := by
      dsimp only [generatorDifference]
      linear_combination (norm := ring1!) h / 2
    exact_mod_cast hc

end MTT.Cohomology
end

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

theorem symmetricPowerChange_basis_val (a b c d : K) {n : ℕ} (j : Fin (n + 1)) :
    (symmetricPowerChange a b c d n (symmetricPowerBasis K n j)).val =
      (a • X 0 + b • X 1) ^ j.val * (c • X 0 + d • X 1) ^ (n - j.val) := by
  change binaryLinearChange a b c d (symmetricPowerBasis K n j).val = _
  rw [symmetricPowerBasis_val_eq]
  simp [binaryLinearChange]

end MTT.Cohomology
end

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
    Module.Basis.repr_self_apply, Finsupp.smul_apply, smul_eq_mul, ite_true, mul_one]

theorem trace_levelOneAction_ST_sq (a b : ℂ) (hab : a ≠ b)
    (ha : a ^ 2 - a + 1 = 0) (hb : b ^ 2 - b + 1 = 0) (n : ℕ) :
    LinearMap.trace ℂ (gammaOneRep 1 n)
      (((gammaOneRep 1 n).ρ (levelOneIncl (ModularGroup.S * ModularGroup.T))) ^ 2) =
        ∑ j : Fin (n + 1), (a ^ j.val * b ^ (n - j.val)) ^ 2 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (ellipticEigenbasis a b hab n), Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, pow_two, Module.End.mul_apply,
    levelOneAction_ST_eigenbasis a b hab ha hb, map_smul,
    Module.Basis.repr_self_apply, Finsupp.smul_apply, smul_eq_mul, ite_true, mul_one]

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

theorem binaryGeometricSum_sq_even (a b : ℂ) (ha : a ^ 2 = -b) (hb : b ^ 2 = -a)
    {n : ℕ} (hn : Even n) :
    (∑ j : Fin (n + 1), (a ^ j.val * b ^ (n - j.val)) ^ 2) =
      ∑ j : Fin (n + 1), a ^ j.val * b ^ (n - j.val) := by
  rw [binaryGeometricSum_comm a b]
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
    _ = _ := by rw [hn.neg_one_pow, one_mul]

theorem trace_levelOneAction_ST_sq_eq {n : ℕ} (hn : Even n)
    (a b : ℂ) (hab : a ≠ b) (ha : a ^ 2 - a + 1 = 0)
    (hb : b ^ 2 - b + 1 = 0) (hs : a + b = 1) :
    LinearMap.trace ℂ (gammaOneRep 1 n)
      (((gammaOneRep 1 n).ρ (levelOneIncl (ModularGroup.S * ModularGroup.T))) ^ 2) =
    LinearMap.trace ℂ (gammaOneRep 1 n)
      ((gammaOneRep 1 n).ρ (levelOneIncl (ModularGroup.S * ModularGroup.T))) := by
  rw [trace_levelOneAction_ST_sq a b hab ha hb, trace_levelOneAction_ST a b hab ha hb]
  apply binaryGeometricSum_sq_even a b _ _ hn
  · linear_combination ha + hs
  · linear_combination hb + hs

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

theorem binaryGeometricSum_even (a b : ℂ) (hab : a ≠ b)
    (ha : a ^ 2 - a + 1 = 0) (hb : b ^ 2 - b + 1 = 0) (m : ℕ) :
    (∑ j : Fin (2 * m + 1), a ^ j.val * b ^ (2 * m - j.val)) =
      if m % 3 = 0 then 1 else if m % 3 = 1 then 0 else -1 := by
  have hpow (x : ℂ) (hx : x ^ 2 - x + 1 = 0) :
      x ^ (2 * m + 1) = x ^ (2 * (m % 3) + 1) := by
    have h3 : x ^ 3 = -1 := by linear_combination (x + 1) * hx
    have h6 : x ^ 6 = 1 := by
      rw [show 6 = 3 * 2 by decide, pow_mul, h3]
      norm_num
    rw [show 2 * m + 1 = 6 * (m / 3) + (2 * (m % 3) + 1) by omega,
      pow_add, pow_mul, h6, one_pow, one_mul]
  have ha3 : a ^ 3 = -1 := by linear_combination (a + 1) * ha
  have hb3 : b ^ 3 = -1 := by linear_combination (b + 1) * hb
  have ha5 : a ^ 5 = 1 - a := by
    calc
      _ = a ^ 3 * a ^ 2 := by ring
      _ = 1 - a := by rw [ha3]; linear_combination -ha
  have hb5 : b ^ 5 = 1 - b := by
    calc
      _ = b ^ 3 * b ^ 2 := by ring
      _ = 1 - b := by rw [hb3]; linear_combination -hb
  apply mul_right_cancel₀ (sub_ne_zero.mpr hab)
  rw [binaryGeometricSum_mul_sub, hpow a ha, hpow b hb]
  have hm : m % 3 < 3 := Nat.mod_lt _ (by decide)
  interval_cases hr : m % 3 <;> norm_num [ha3, hb3, ha5, hb5]

theorem trace_levelOneAction_ST_even (m : ℕ) :
    LinearMap.trace ℂ (gammaOneRep 1 (2 * m))
      ((gammaOneRep 1 (2 * m)).ρ (levelOneIncl (ModularGroup.S * ModularGroup.T))) =
        if m % 3 = 0 then 1 else if m % 3 = 1 then 0 else -1 := by
  obtain ⟨a, b, hab, ha, hb, _⟩ := exists_elliptic_eigenvalues
  rw [trace_levelOneAction_ST a b hab ha hb, binaryGeometricSum_even a b hab ha hb]

theorem finrank_ellipticFixed (m : ℕ) :
    Module.finrank ℂ (generatorDifference (2 * m) (ModularGroup.S * ModularGroup.T)).ker =
      2 * (m / 3) + 1 := by
  have : FiniteDimensional ℂ (gammaOneRep 1 (2 * m)) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 2) ℂ (2 * m))
  have hn : Even (2 * m) := ⟨m, by omega⟩
  have h := LinearMap.three_mul_finrank_fixed_eq_trace
    (V := gammaOneRep 1 (2 * m))
    ((gammaOneRep 1 (2 * m)).ρ (levelOneIncl (ModularGroup.S * ModularGroup.T)))
    (levelOneAction_ST_cubic hn)
  obtain ⟨a, b, hab, ha, hb, hs⟩ := exists_elliptic_eigenvalues
  rw [trace_levelOneAction_ST_sq_eq hn a b hab ha hb hs,
    trace_levelOneAction_ST_even, show Module.finrank ℂ (gammaOneRep 1 (2 * m)) = 2 * m + 1
      from finrank_sym (2 * m)] at h
  have hm : (m : ℂ) = 3 * (m / 3 : ℕ) + (m % 3 : ℕ) := by
    exact_mod_cast (Nat.mod_add_div m 3).symm.trans (by omega)
  push_cast at h
  have hlt : m % 3 < 3 := Nat.mod_lt _ (by decide)
  have hc :
      (Module.finrank ℂ
        (generatorDifference (2 * m) (ModularGroup.S * ModularGroup.T)).ker : ℂ) =
      2 * (m / 3 : ℕ) + 1 := by
    dsimp only [generatorDifference]
    interval_cases hr : m % 3 <;> norm_num at h hm <;>
      linear_combination (norm := ring1!) h / 3 + (2 / 3 : ℂ) * hm
  exact_mod_cast hc

end MTT.Cohomology
end

/-! # Degree-zero parabolic cohomology at level one -/

noncomputable section

namespace MTT.Cohomology

theorem act_homogeneous_zero {R : Type*} [CommRing R]
    (A : Matrix (Fin 2) (Fin 2) ℤ) {P : Binary R} (hP : P ∈ Sym R 0) : act A P = P := by
  have hconst : P = MvPolynomial.C (AddMonoidAlgebra.coeff P 0) :=
    (MvPolynomial.homogeneousComponent_eq_self hP).symm.trans
      (MvPolynomial.homogeneousComponent_zero P)
  rw [hconst]
  exact MvPolynomial.bind₁_C_right _ _

private theorem gammaOneRep_zero_apply (N : ℕ) (g : CongruenceSubgroup.Gamma1 N)
    (P : gammaOneRep N 0) : (gammaOneRep N 0).ρ g P = P :=
  Subtype.ext (act_homogeneous_zero _ P.property)

theorem parabolicCocycle_level_one_degree_zero (c : parabolicCocycles 1 0) : c = 0 := by
  let incl : Matrix.SpecialLinearGroup (Fin 2) ℤ →* CongruenceSubgroup.Gamma1 1 :=
    { toFun g := ⟨g, by
        rw [CongruenceSubgroup.Gamma1_mem]
        exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hc (g h : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
      c.val (incl (g * h)) = c.val (incl g) + c.val (incl h) := by
    rw [map_mul, ((mem_parabolicCocycles_iff _).mp c.property).1,
      gammaOneRep_zero_apply, add_comm]
  have h0 : c.val (incl 1) = 0 := by
    exact groupCohomology.cocycles₁_map_one ⟨c.val, c.property.1⟩
  have hS : c.val (incl ModularGroup.S) = 0 := by
    have hS₄ : ModularGroup.S * ModularGroup.S *
        (ModularGroup.S * ModularGroup.S) = 1 := by decide
    have heq := congrArg (fun g => c.val (incl g)) hS₄
    rw [hc, hc, h0] at heq
    have hscale : (4 : ℂ) • c.val (incl ModularGroup.S) = 0 := by
      calc
        _ = c.val (incl ModularGroup.S) + c.val (incl ModularGroup.S) +
            (c.val (incl ModularGroup.S) + c.val (incl ModularGroup.S)) := by module
        _ = 0 := heq
    exact (smul_eq_zero.mp hscale).resolve_left (by norm_num)
  have hT : c.val (incl ModularGroup.T) = 0 := by
    obtain ⟨P, hP⟩ := ((mem_parabolicCocycles_iff _).mp c.property).2 OnePoint.infty
      (incl ModularGroup.T) (by
        change Matrix.SpecialLinearGroup.mapGL ℚ ModularGroup.T • OnePoint.infty = _
        exact OnePoint.smul_infty_eq_self_iff.mpr rfl)
    simpa only [gammaOneRep_zero_apply, sub_self] using hP
  have hall (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) : c.val (incl g) = 0 := by
    have hg : g ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} :=
      SpecialLinearGroup.SL2Z_generators.symm ▸ Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem g hg => rcases hg with rfl | rfl; exact hS; exact hT
    | one => exact h0
    | mul g h _ _ hg hh => rw [hc, hg, hh, add_zero]
    | inv g _ hg =>
        have heq := hc g⁻¹ g
        simpa only [inv_mul_cancel, h0, hg, add_zero] using heq.symm
  apply Subtype.ext
  funext g
  exact hall g.val

theorem parabolicH1_level_one_degree_zero : Subsingleton (ParabolicH1 1 0) := by
  have : Subsingleton (parabolicCocycles 1 0) :=
    ⟨fun c d => (parabolicCocycle_level_one_degree_zero c).trans
      (parabolicCocycle_level_one_degree_zero d).symm⟩
  infer_instance

end MTT.Cohomology
end

/-! # The parabolic cohomology dimension bound at level one -/

noncomputable section

namespace MTT.Cohomology

open MatrixGroups

theorem periodRelations_finrank_even (m : ℕ) (hm : 0 < m) :
    Module.finrank ℂ (periodRelations (2 * m)) + 2 * (m / 3) +
      (if Even m then 1 else 0) = m := by
  have h := periodRelations_finrank_add_fixed_finranks
    (show Even (2 * m) from ⟨m, by omega⟩) (show 0 < 2 * m by omega)
  rw [finrank_inversionFixed, finrank_ellipticFixed] at h
  omega

theorem GammaOne_one_eq : GammaOne 1 = 𝒮ℒ := by
  have h : CongruenceSubgroup.Gamma1 1 = ⊤ := by
    ext g
    simp only [Subgroup.mem_top, iff_true]
    exact (levelOneIncl g).property
  ext g
  simp only [GammaOne, h, Subgroup.mem_map, Subgroup.mem_top, true_and, MonoidHom.mem_range]

private theorem cuspForm_finrank_congr
    {G H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} [G.HasDetOne] [H.HasDetOne]
    (h : G = H) (k : ℤ) :
    Module.finrank ℂ (CuspForm G k) = Module.finrank ℂ (CuspForm H k) := by
  subst H
  rfl

theorem levelOne_cusp_finrank_formula (m : ℕ) (hm : 0 < m) :
    2 * Module.finrank ℂ (CuspForm (GammaOne 1) ((2 * m + 2 : ℕ) : ℤ)) + 1 +
      2 * (m / 3) + (if Even m then 1 else 0) = m := by
  rw [cuspForm_finrank_congr GammaOne_one_eq]
  have : FiniteDimensional ℂ (CuspForm 𝒮ℒ ((2 * m + 2 : ℕ) : ℤ)) :=
    FiniteDimensional.of_injective CuspForm.discriminantEquiv.toLinearMap
      CuspForm.discriminantEquiv.injective
  have heven : Even (2 * m + 2) := ⟨m + 1, by omega⟩
  have h := ModularForm.rank_eq_one_add_rank_cuspForm (show 3 ≤ 2 * m + 2 by omega) heven
  rw [ModularForm.dimension_level_one _ heven] at h
  rw [← Module.finrank_eq_rank ℂ (CuspForm 𝒮ℒ ((2 * m + 2 : ℕ) : ℤ))] at h
  have h' : (if (2 * m + 2) % 12 = 2 then (2 * m + 2) / 12
      else (2 * m + 2) / 12 + 1) =
      1 + Module.finrank ℂ (CuspForm 𝒮ℒ ((2 * m + 2 : ℕ) : ℤ)) := by
    simp only [Nat.ModEq, show 2 % 12 = 2 from rfl] at h
    exact_mod_cast h
  by_cases hp : Even m
  · rw [ite_eq_left hp]
    obtain ⟨r, hr⟩ := hp
    have hd : m % 2 = 0 := by omega
    split_ifs at h' <;> omega
  · rw [ite_eq_right hp]
    have hd : m % 2 = 1 := Nat.mod_two_ne_zero.mp (fun h => hp (even_iff_two_dvd.mpr
      (Nat.dvd_of_mod_eq_zero h)))
    split_ifs at h' <;> omega

theorem periodRelations_finrank_eq_twice_cusp_add_one (m : ℕ) (hm : 0 < m) :
    Module.finrank ℂ (periodRelations (2 * m)) =
      2 * Module.finrank ℂ (CuspForm (GammaOne 1) ((2 * m + 2 : ℕ) : ℤ)) + 1 := by
  have h := periodRelations_finrank_even m hm
  have hc := levelOne_cusp_finrank_formula m hm
  omega

theorem parabolicH1_level_one_finrank_le (n : ℕ) :
    Module.finrank ℂ (ParabolicH1 1 n) ≤
      2 * Module.finrank ℂ (CuspForm (GammaOne 1) ((n + 2 : ℕ) : ℤ)) := by
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨m, hm⟩ := hn
    obtain rfl : n = 2 * m := by omega
    by_cases hm0 : m = 0
    · subst m
      have : Subsingleton (ParabolicH1 1 (2 * 0)) := parabolicH1_level_one_degree_zero
      rw [Module.finrank_eq_zero_of_subsingleton]
      exact Nat.zero_le _
    · have h := parabolicH1_add_one_le_periodRelations
        (show Even (2 * m) from ⟨m, by omega⟩) (show 0 < 2 * m by omega)
      rw [periodRelations_finrank_eq_twice_cusp_add_one m (by omega)] at h
      omega
  · have := parabolicH1_subsingleton_of_odd_small_level (by decide : 0 < 1)
      (by decide : 1 ≤ 2) hn
    rw [Module.finrank_eq_zero_of_subsingleton]
    exact Nat.zero_le _

theorem parabolicH1_dimension_bound_levelOne {k : ℕ} (hk : 2 ≤ k) :
    Module.finrank ℂ (ParabolicH1 1 (k - 2)) ≤
      2 * Module.finrank ℂ (CuspForm (GammaOne 1) (k : ℤ)) := by
  exact (parabolicH1_level_one_finrank_le (k - 2)).trans_eq
    (congrArg (fun j : ℕ => 2 * Module.finrank ℂ (CuspForm (GammaOne 1) (j : ℤ)))
      (Nat.sub_add_cancel hk))

end MTT.Cohomology
end

/-- The level-one specialization of the MTT parabolic dimension bound. -/
theorem solution {k : ℕ} (hk : 2 ≤ k) :
    Module.finrank ℂ (MTT.Cohomology.ParabolicH1 1 (k - 2)) ≤
      2 * Module.finrank ℂ (CuspForm (MTT.GammaOne 1) (k : ℤ)) :=
  MTT.Cohomology.parabolicH1_dimension_bound_levelOne hk

end privateSection

public section publicSection

noncomputable section

theorem MTT.Cohomology.parabolicH1_finrank_le_level_one {k : ℕ} (hk : 2 ≤ k) :
    Module.finrank ℂ (MTT.Cohomology.ParabolicH1 1 (k - 2)) ≤
      2 * Module.finrank ℂ (CuspForm (MTT.GammaOne 1) (k : ℤ)) := _root_.solution hk
end

end publicSection
