import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.GroupTheory.Schreier
import Mathlib.RepresentationTheory.FiniteIndex

import Definitions.MTT.Def_MTT_FullParabolicCohomology
import Definitions.MTT.Def_MTT_NormalizedParabolicCocycles
import Theorems.FLT.Thm_HeckeEis_exists_eq_smul_X_pow_of_binaryFormRepSL_T_zpow_eq_self
import Theorems.FLT.Thm_HeckeEis_finrank_coeffH1par_top_add_le
import Theorems.FLT.Thm_Rep_finiteDimensional_coind_and_finrank_coind_eq_index_mul

/-! # The central-fixed coinduced cohomology bound via three fixed spaces -/

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

end MTT.Cohomology

section

namespace MTT.Cohomology

open MvPolynomial

def gammaOneLower (N : ℕ) : CongruenceSubgroup.Gamma1 N := by
  let g : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![1, 0; (N : ℤ), 1], by simp [Matrix.det_fin_two]⟩
  refine ⟨g, ?_⟩
  rw [CongruenceSubgroup.Gamma1_mem]
  simp [g]

def xPowerAtLevel (N n : ℕ) : gammaOneRep N n :=
  ⟨X 0 ^ n, isHomogeneous_X_pow 0 n⟩

theorem xPowerAtLevel_T_invariant (N n : ℕ) :
    (gammaOneRep N n).ρ (gammaOneT N) (xPowerAtLevel N n) = xPowerAtLevel N n := by
  apply Subtype.ext
  change act ModularGroup.T.val (X 0 ^ n : Binary ℂ) = X 0 ^ n
  change MvPolynomial.aeval _ (X 0 ^ n : Binary ℂ) = _
  simp [ModularGroup.T, Fin.sum_univ_two]

theorem gammaOne_T_invariant_eq_smul {N n : ℕ} (P : gammaOneRep N n)
    (hP : (gammaOneRep N n).ρ (gammaOneT N) P = P) :
    ∃ a : ℂ, P = a • xPowerAtLevel N n := by
  have hb : HeckeEis.binaryFormRepSL ℂ n (ModularGroup.T ^ (1 : ℤ)) P = P := by
    rw [zpow_one]
    apply Subtype.ext
    have h := congrArg Subtype.val hP
    change act ModularGroup.T.val P.val = P.val at h
    change HeckeEis.binarySubst ℂ ModularGroup.T.val P.val = P.val
    simpa only [act, HeckeEis.binarySubst, MvPolynomial.C_mul',
      AlgHom.toLinearMap_apply] using h
  obtain ⟨a, ha⟩ := HeckeEis.exists_eq_smul_X_pow_of_binaryFormRepSL_T_zpow_eq_self n
    (by norm_num : ((1 : ℤ) : ℂ) ≠ 0)
    (fun j hj _ => by exact_mod_cast Nat.ne_of_gt hj) P hb
  exact ⟨a, Subtype.ext ha⟩

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

theorem gammaOneRep_invariant_eq_zero {N n : ℕ} (hN : 0 < N) (hn : 0 < n)
    (P : gammaOneRep N n) (hP : ∀ g, (gammaOneRep N n).ρ g P = P) : P = 0 := by
  obtain ⟨a, rfl⟩ := gammaOne_T_invariant_eq_smul P (hP (gammaOneT N))
  have h := congrArg (fun Q : gammaOneRep N n => eval ![(0 : ℂ), 1] Q.val)
    (hP (gammaOneLower N))
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  change eval ![(0 : ℂ), 1] (act !![1, 0; (N : ℤ), 1] (a • X 0 ^ n)) =
    eval ![(0 : ℂ), 1] (a • X 0 ^ n) at h
  have ha : a = 0 := by simpa [eval_act, Nat.ne_of_gt hn, hN0] using h
  rw [ha, zero_smul]

def gammaOneDifference (N n : ℕ) (g : CongruenceSubgroup.Gamma1 N) :
    Module.End ℂ (gammaOneRep N n) := (gammaOneRep N n).ρ g - LinearMap.id

theorem gammaOneDifference_translation_range_finrank (N n : ℕ) :
    Module.finrank ℂ (gammaOneDifference N n (gammaOneT N)).range = n := by
  have : FiniteDimensional ℂ (gammaOneRep N n) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 2) ℂ n)
  have hk : (gammaOneDifference N n (gammaOneT N)).ker =
      Submodule.span ℂ {xPowerAtLevel N n} := by
    ext P
    rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
    change (gammaOneRep N n).ρ (gammaOneT N) P - P = 0 ↔ _
    rw [sub_eq_zero]
    constructor
    · intro hP
      obtain ⟨a, ha⟩ := gammaOne_T_invariant_eq_smul P hP
      exact ⟨a, ha.symm⟩
    · rintro ⟨a, rfl⟩
      rw [map_smul, xPowerAtLevel_T_invariant]
  have hx : xPowerAtLevel N n ≠ 0 := by
    intro h
    exact pow_ne_zero n (MvPolynomial.X_ne_zero (0 : Fin 2)) (congrArg Subtype.val h)
  have hd := (gammaOneDifference N n (gammaOneT N)).finrank_range_add_finrank_ker
  rw [hk, finrank_span_singleton hx] at hd
  change _ + 1 = Module.finrank ℂ (Sym ℂ n) at hd
  rw [finrank_sym] at hd
  omega

theorem eval_y_gammaOneDifference (N n : ℕ) (P : gammaOneRep N n) :
    eval ![(0 : ℂ), 1] (gammaOneDifference N n (gammaOneT N) P).val = 0 := by
  change eval ![(0 : ℂ), 1] (act ModularGroup.T.val P.val - P.val) = 0
  simp [eval_sub, eval_act, ModularGroup.T]

end MTT.Cohomology

section
namespace MTT.Cohomology

theorem gammaOneLower_difference_notMem_translation_range {N n : ℕ}
    (hN : 0 < N) (hn : 0 < n) :
    gammaOneDifference N n (gammaOneLower N) (xPowerAtLevel N n) ∉
      (gammaOneDifference N n (gammaOneT N)).range := by
  rintro ⟨P, hP⟩
  have h : MvPolynomial.eval ![(0 : ℂ), 1]
      (gammaOneDifference N n (gammaOneT N) P).val = 0 :=
    eval_y_gammaOneDifference N n P
  rw [hP] at h
  change MvPolynomial.eval ![(0 : ℂ), 1]
    (act !![1, 0; (N : ℤ), 1] (MvPolynomial.X 0 ^ n) - MvPolynomial.X 0 ^ n) = 0 at h
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  simp [MvPolynomial.eval_sub, eval_act, Nat.ne_of_gt hn, hN0] at h

theorem gammaOne_difference_ranges_eq_top {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    (gammaOneDifference N n (gammaOneT N)).range ⊔
      (gammaOneDifference N n (gammaOneLower N)).range = ⊤ := by
  have : FiniteDimensional ℂ (gammaOneRep N n) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 2) ℂ n)
  have ht : (gammaOneDifference N n (gammaOneT N)).range ⊔
      Submodule.span ℂ {gammaOneDifference N n (gammaOneLower N) (xPowerAtLevel N n)} = ⊤ := by
    apply Submodule.eq_top_iff_finrank_eq.mpr
    rw [Submodule.finrank_sup_span_singleton
      (gammaOneLower_difference_notMem_translation_range hN hn),
      gammaOneDifference_translation_range_finrank]
    exact (finrank_sym n).symm
  apply top_unique
  rw [← ht]
  apply sup_le_sup_left
  exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ⟨xPowerAtLevel N n, rfl⟩)

theorem gammaOne_coinvariants_ker_eq_top {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    Representation.Coinvariants.ker (gammaOneRep N n).ρ = ⊤ := by
  apply top_unique
  rw [← gammaOne_difference_ranges_eq_top hN hn]
  apply sup_le
  · rintro P ⟨Q, rfl⟩
    exact Representation.Coinvariants.sub_mem_ker (gammaOneT N) Q
  · rintro P ⟨Q, rfl⟩
    exact Representation.Coinvariants.sub_mem_ker (gammaOneLower N) Q

end MTT.Cohomology

section
namespace MTT.Cohomology

theorem coinduced_invariant_eq_zero {N n : ℕ} (hN : 0 < N) (hn : 0 < n)
    (f : Rep.coind (CongruenceSubgroup.Gamma1 N).subtype (gammaOneRep N n))
    (hf : ∀ g, (Rep.coind (CongruenceSubgroup.Gamma1 N).subtype
      (gammaOneRep N n)).ρ g f = f) : f = 0 := by
  have hconst (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) : f.val g = f.val 1 := by
    have h := congrArg (fun P => P.val 1) (hf g)
    change f.val (1 * g) = f.val 1 at h
    simpa only [one_mul] using h
  have h1 : f.val 1 = 0 := gammaOneRep_invariant_eq_zero hN hn (f.val 1) fun h => by
    have hh := f.property h 1
    change f.val (h.val * 1) = (gammaOneRep N n).ρ h (f.val 1) at hh
    rw [mul_one, hconst] at hh
    exact hh.symm
  apply Subtype.ext
  funext g
  exact (hconst g).trans h1

theorem centralCoinduced_invariant_eq_zero {N n : ℕ} (hN : 0 < N) (hn : 0 < n)
    (f : centralCoinduced N n) (hf : ∀ g, (centralCoinduced N n).ρ g f = f) : f = 0 := by
  apply Subtype.ext
  exact coinduced_invariant_eq_zero hN hn f.val fun g => congrArg Subtype.val (hf g)

end MTT.Cohomology

section

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

theorem centralFixedRep_action (v : centralFixedRep A z hz) :
    (centralFixedRep A z hz).ρ z v = v :=
  Subtype.ext ((mem_centralFixed A z v.val).mp v.property)

theorem centralAverage_fixed (v : centralFixedRep A z hz) :
    centralAverage A z hz hz₂ v.val = v := by
  apply Subtype.ext
  change (2 : ℂ)⁻¹ • (v.val + A.ρ z v.val) = v.val
  rw [(mem_centralFixed A z v.val).mp v.property]
  module

end Rep

section

namespace MTT.Cohomology

open CategoryTheory

theorem gammaOne_invariantLinear_eq_zero {N n : ℕ} (hN : 0 < N) (hn : 0 < n)
    {Q : Type} [AddCommGroup Q] [Module ℂ Q] (f : gammaOneRep N n →ₗ[ℂ] Q)
    (hf : ∀ g P, f ((gammaOneRep N n).ρ g P) = f P) : f = 0 := by
  have hle : Representation.Coinvariants.ker (gammaOneRep N n).ρ ≤ f.ker := by
    apply Submodule.span_le.mpr
    rintro v ⟨⟨g, P⟩, rfl⟩
    change f ((gammaOneRep N n).ρ g P - P) = 0
    rw [map_sub, hf, sub_self]
  rw [gammaOne_coinvariants_ker_eq_top hN hn] at hle
  ext P
  exact hle (Submodule.mem_top : P ∈ (⊤ : Submodule ℂ (gammaOneRep N n)))

theorem coinduced_invariantLinear_eq_zero {N n : ℕ} (hN : 0 < N) (hn : 0 < n)
    {Q : Type} [AddCommGroup Q] [Module ℂ Q]
    (f : Rep.coind (CongruenceSubgroup.Gamma1 N).subtype (gammaOneRep N n) →ₗ[ℂ] Q)
    (hf : ∀ g P, f ((Rep.coind (CongruenceSubgroup.Gamma1 N).subtype
      (gammaOneRep N n)).ρ g P) = f P) : f = 0 := by
  classical
  have : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let B := Rep.trivial ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) Q
  let F : Rep.coind (CongruenceSubgroup.Gamma1 N).subtype (gammaOneRep N n) ⟶ B :=
    Rep.ofHom ⟨f, fun g => LinearMap.ext (hf g)⟩
  let e := (Rep.coindResAdjunction ℂ (CongruenceSubgroup.Gamma1 N)).homEquiv
    (gammaOneRep N n) B
  have he : e F = 0 := by
    have hh := gammaOne_invariantLinear_eq_zero hN hn (e F).hom.toLinearMap
      (fun g P => Rep.hom_comm_apply (e F) g P)
    ext P
    exact congrArg (fun l : gammaOneRep N n →ₗ[ℂ] Q => l P) hh
  have hF : F = 0 := by
    apply e.injective
    rw [he]
    change 0 = (Rep.coindResAdjunction ℂ (CongruenceSubgroup.Gamma1 N)).homEquiv _ _ 0
    rw [Rep.coindResAdjunction_homEquiv_apply]
    have hz : (Rep.indCoindIso (gammaOneRep N n)).hom ≫
        (0 : Rep.coind (CongruenceSubgroup.Gamma1 N).subtype (gammaOneRep N n) ⟶ B) = 0 := by
      ext P
      rfl
    rw [hz]
    exact (map_zero (Rep.indResHomEquiv _ _ _)).symm
  exact congrArg (fun l => l.hom.toLinearMap) hF

theorem centralCoinduced_invariantLinear_eq_zero {N n : ℕ} (hN : 0 < N) (hn : 0 < n)
    {Q : Type} [AddCommGroup Q] [Module ℂ Q]
    (f : centralCoinduced N n →ₗ[ℂ] Q)
    (hf : ∀ g P, f ((centralCoinduced N n).ρ g P) = f P) : f = 0 := by
  let p := Rep.centralAverage
    (Rep.coind (CongruenceSubgroup.Gamma1 N).subtype (gammaOneRep N n))
      (-1) neg_one_central (by simp only [neg_mul_neg, one_mul])
  have h := coinduced_invariantLinear_eq_zero hN hn (f.comp p) (fun g P => by
    change f (p (_)) = f (p P)
    rw [Rep.centralAverage_comm, hf])
  ext P
  have hP := congrArg (fun l => l P.val) h
  change f (p P.val) = 0 at hP
  rw [Rep.centralAverage_fixed] at hP
  exact hP

end MTT.Cohomology

section

namespace Rep

variable {G : Type} [Group G] (A : Rep ℂ G)

theorem invariantLinear_of_generators {Q : Type} [AddCommGroup Q] [Module ℂ Q]
    (f : A →ₗ[ℂ] Q) {s : Set G} (hs : Subgroup.closure s = ⊤)
    (hf : ∀ g ∈ s, ∀ v, f (A.ρ g v) = f v) (g : G) (v : A) :
    f (A.ρ g v) = f v := by
  have hg : g ∈ Subgroup.closure s := hs ▸ Subgroup.mem_top g
  induction hg using Subgroup.closure_induction generalizing v with
  | mem g hg => exact hf g hg v
  | one => rw [map_one]; rfl
  | mul g h _ _ ihg ihh => rw [map_mul, Module.End.mul_apply, ihg, ihh]
  | inv g _ ih =>
      have h := ih (A.ρ g⁻¹ v)
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one] at h
      exact h.symm

end Rep

namespace MTT.Cohomology

theorem invariantLinear_of_S_ST
    (A : Rep ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    {Q : Type} [AddCommGroup Q] [Module ℂ Q] (f : A →ₗ[ℂ] Q)
    (hS : ∀ v, f (A.ρ ModularGroup.S v) = f v)
    (hU : ∀ v, f (A.ρ (ModularGroup.S * ModularGroup.T) v) = f v)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (v : A) : f (A.ρ g v) = f v := by
  have hT (w : A) : f (A.ρ ModularGroup.T w) = f w := by
    calc
      f (A.ρ ModularGroup.T w) = f (A.ρ ModularGroup.S (A.ρ ModularGroup.T w)) :=
        (hS _).symm
      _ = f (A.ρ (ModularGroup.S * ModularGroup.T) w) := by
        rw [map_mul, Module.End.mul_apply]
      _ = f w := hU w
  apply Rep.invariantLinear_of_generators A f SpecialLinearGroup.SL2Z_generators _ g v
  intro a ha w
  rcases ha with rfl | rfl
  · exact hS w
  · exact hT w

theorem centralCoinduced_generator_ranges_eq_top {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    ((centralCoinduced N n).ρ ModularGroup.S - LinearMap.id).range ⊔
      ((centralCoinduced N n).ρ (ModularGroup.S * ModularGroup.T) - LinearMap.id).range = ⊤ := by
  let R := ((centralCoinduced N n).ρ ModularGroup.S - LinearMap.id).range ⊔
    ((centralCoinduced N n).ρ (ModularGroup.S * ModularGroup.T) - LinearMap.id).range
  have hS (v : centralCoinduced N n) :
      R.mkQ ((centralCoinduced N n).ρ ModularGroup.S v) = R.mkQ v := by
    apply (Submodule.Quotient.eq R).mpr
    exact Submodule.mem_sup_left ⟨v, rfl⟩
  have hU (v : centralCoinduced N n) :
      R.mkQ ((centralCoinduced N n).ρ (ModularGroup.S * ModularGroup.T) v) = R.mkQ v := by
    apply (Submodule.Quotient.eq R).mpr
    exact Submodule.mem_sup_right ⟨v, rfl⟩
  have hz := centralCoinduced_invariantLinear_eq_zero hN hn R.mkQ
    (invariantLinear_of_S_ST _ R.mkQ hS hU)
  have hk := congrArg LinearMap.ker hz
  simpa only [Submodule.ker_mkQ, LinearMap.ker_zero] using hk

end MTT.Cohomology

section

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

/-- Finite generation of the group bounds the dimension of the one-cocycle space. -/
theorem finiteDimensional_cocycles₁ [Group.FG G] [FiniteDimensional K A] :
    FiniteDimensional K (cocycles₁ A) := by
  classical
  obtain ⟨s, hs, hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  let : Fintype s := hfin.fintype
  let ev : cocycles₁ A →ₗ[K] (s → A) :=
    LinearMap.pi fun x => (LinearMap.proj (x : G)).comp (cocycles₁ A).subtype
  apply FiniteDimensional.of_injective ev
  intro f g hfg
  apply cocycles₁_ext_of_generators hs
  intro x hx
  exact congrFun hfg ⟨x, hx⟩

end groupCohomology

section
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

section

namespace MTT.Cohomology

open groupCohomology

variable (A : Rep ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ))

abbrev topCoeffRep := A.ρ.comp (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)).subtype

def fullToCoeffParabolic : fullParabolicCocycles A →ₗ[ℂ]
    HeckeEis.coeffParabolicCocycles (topCoeffRep A) where
  toFun c := ⟨fun g => c.val g.val, by
    obtain ⟨hc, hp⟩ := (mem_fullParabolicCocycles_iff _ _).mp c.property
    constructor
    · intro g h
      change c.val (g.val * h.val) = c.val g.val + A.ρ g.val (c.val h.val)
      rw [(mem_cocycles₁_iff _).mp hc]
      exact add_comm _ _
    · intro g hg
      obtain ⟨x, hx⟩ := exists_cusp_fixed_of_trace_sq g.val hg
      exact hp x g.val hx⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def fullToCoeffClass : fullParabolicCocycles A →ₗ[ℂ]
    HeckeEis.coeffH1par (topCoeffRep A) :=
  (HeckeEis.coeffH1parMk _).comp (fullToCoeffParabolic A)

theorem fullToCoeffClass_ker : (fullToCoeffClass A).ker = fullParabolicCoboundaries A := by
  ext c
  change HeckeEis.coeffH1parMk _ (fullToCoeffParabolic A c) = 0 ↔ _
  rw [HeckeEis.coeffH1parMk_eq_zero_iff, HeckeEis.mem_coeffCoboundaries_iff]
  change (∃ P, (fun g : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) =>
    A.ρ g.val P - P) = fun g => c.val g.val) ↔
    c.val ∈ coboundaries₁ A
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨P, funext fun g => congrFun hP ⟨g, Subgroup.mem_top g⟩⟩
  · rintro ⟨P, hP⟩
    exact ⟨P, funext fun g => congrFun hP g.val⟩

def fullToCoeffH1 : FullParabolicH1 A →ₗ[ℂ] HeckeEis.coeffH1par (topCoeffRep A) :=
  (fullParabolicCoboundaries A).liftQ (fullToCoeffClass A) (fullToCoeffClass_ker A).ge

theorem fullToCoeffH1_injective : Function.Injective (fullToCoeffH1 A) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot _ _ _ (fullToCoeffClass_ker A).le

theorem coeffCocycles_eq_cocycles₁ {G : Type} [Group G] (B : Rep ℂ G) :
    HeckeEis.coeffCocycles B.ρ = cocycles₁ B := by
  ext c
  rw [HeckeEis.mem_coeffCocycles_iff, mem_cocycles₁_iff]
  simp only [add_comm]

theorem topCoeffH1_finiteDimensional [FiniteDimensional ℂ A] :
    FiniteDimensional ℂ (HeckeEis.coeffH1par (topCoeffRep A)) := by
  have : Group.FG (Matrix.SpecialLinearGroup (Fin 2) ℤ) :=
    Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T},
      SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩
  have : FiniteDimensional ℂ (HeckeEis.coeffCocycles (topCoeffRep A)) := by
    rw [coeffCocycles_eq_cocycles₁ (Rep.of (topCoeffRep A))]
    exact groupCohomology.finiteDimensional_cocycles₁ (A := Rep.of (topCoeffRep A))
  have : FiniteDimensional ℂ (HeckeEis.coeffParabolicCocycles (topCoeffRep A)) :=
    FiniteDimensional.of_injective
      (Submodule.inclusion (HeckeEis.coeffParabolicCocycles_le_coeffCocycles _))
      (Submodule.inclusion_injective _)
  exact Module.Finite.of_surjective (HeckeEis.coeffH1parMk (topCoeffRep A))
    (HeckeEis.coeffH1parMk_surjective _)

theorem fullParabolicH1_finrank_le_topCoeffH1 [FiniteDimensional ℂ A] :
    Module.finrank ℂ (FullParabolicH1 A) ≤
      Module.finrank ℂ (HeckeEis.coeffH1par (topCoeffRep A)) := by
  have := topCoeffH1_finiteDimensional A
  exact LinearMap.finrank_le_finrank_of_injective (fullToCoeffH1_injective A)

end MTT.Cohomology

section

namespace MTT.Cohomology

theorem centralCoinduced_parabolicH1_add_fixed_finrank_le {N n : ℕ}
    (hN : 0 < N) (hn : 0 < n) :
    Module.finrank ℂ (FullParabolicH1 (centralCoinduced N n)) +
        Module.finrank ℂ ((centralCoinduced N n).ρ ModularGroup.S - LinearMap.id).ker +
        Module.finrank ℂ
          ((centralCoinduced N n).ρ (ModularGroup.S * ModularGroup.T) - LinearMap.id).ker +
        Module.finrank ℂ ((centralCoinduced N n).ρ ModularGroup.T - LinearMap.id).ker ≤
      Module.finrank ℂ (centralCoinduced N n) := by
  have : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have : FiniteDimensional ℂ (gammaOneRep N n) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 2) ℂ n)
  have := (Rep.finiteDimensional_coind_and_finrank_coind_eq_index_mul
    (CongruenceSubgroup.Gamma1 N) (gammaOneRep N n)).1
  have hneg : topCoeffRep (centralCoinduced N n) ⟨-1, Subgroup.mem_top _⟩ = LinearMap.id := by
    apply LinearMap.ext
    intro v
    exact Rep.centralFixedRep_action _ _ _ v
  have hinv : ∀ v : centralCoinduced N n,
      (∀ g, topCoeffRep (centralCoinduced N n) g v = v) → v = 0 := by
    intro v hv
    exact centralCoinduced_invariant_eq_zero hN hn v
      (fun g => hv ⟨g, Subgroup.mem_top _⟩)
  have hcoinv : ∀ v : centralCoinduced N n, ∃ a b : centralCoinduced N n,
      v = ((centralCoinduced N n).ρ ModularGroup.S a - a) +
        ((centralCoinduced N n).ρ (ModularGroup.S * ModularGroup.T) b - b) := by
    intro v
    have hv : v ∈ ((centralCoinduced N n).ρ ModularGroup.S - LinearMap.id).range ⊔
        ((centralCoinduced N n).ρ (ModularGroup.S * ModularGroup.T) - LinearMap.id).range := by
      rw [centralCoinduced_generator_ranges_eq_top hN hn]
      trivial
    obtain ⟨x, ⟨a, rfl⟩, y, ⟨b, rfl⟩, hab⟩ := Submodule.mem_sup.mp hv
    exact ⟨a, b, hab.symm⟩
  have h := HeckeEis.finrank_coeffH1par_top_add_le
    (topCoeffRep (centralCoinduced N n)) hneg hinv hcoinv
  have hc := fullParabolicH1_finrank_le_topCoeffH1 (centralCoinduced N n)
  exact le_trans (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right hc _) _) _) h

end MTT.Cohomology

theorem solution {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    Module.finrank ℂ (MTT.Cohomology.FullParabolicH1 (MTT.Cohomology.centralCoinduced N n)) +
        Module.finrank ℂ ((MTT.Cohomology.centralCoinduced N n).ρ
          ModularGroup.S - LinearMap.id).ker +
        Module.finrank ℂ ((MTT.Cohomology.centralCoinduced N n).ρ
          (ModularGroup.S * ModularGroup.T) - LinearMap.id).ker +
        Module.finrank ℂ ((MTT.Cohomology.centralCoinduced N n).ρ
          ModularGroup.T - LinearMap.id).ker ≤
      Module.finrank ℂ (MTT.Cohomology.centralCoinduced N n) :=
  MTT.Cohomology.centralCoinduced_parabolicH1_add_fixed_finrank_le hN hn
