import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.CommRing
import Definitions.MTT.Def_MTT_Cohomology
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.GroupTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Definitions.MTT.Def_MTT_NormalizedParabolicCocycles

set_option autoImplicit false

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
end

/-!
# Finite-dimensional parabolic cohomology for Gamma1(N)

SL2(Z) is generated by S and T; Schreier's theorem gives finite generation of
Gamma1(N) for positive N. Its homogeneous binary coefficient module is finite,
and the cocycle space embeds in a finite product of that module. Subspaces and
quotients preserve finite-dimensionality. No cusp-form dimension formula is used.
-/

noncomputable section

namespace MTT.Cohomology

open groupCohomology

theorem finiteDimensional_parabolicCocycles (N n : ℕ) [NeZero N] :
    FiniteDimensional ℂ (parabolicCocycles N n) := by
  have : Group.FG (Matrix.SpecialLinearGroup (Fin 2) ℤ) :=
    Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T},
      SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩
  have : FiniteDimensional ℂ (gammaOneRep N n) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 2) ℂ n)
  have : FiniteDimensional ℂ (cocycles₁ (gammaOneRep N n)) := finiteDimensional_cocycles₁
  let ι : parabolicCocycles N n →ₗ[ℂ] cocycles₁ (gammaOneRep N n) :=
    Submodule.inclusion (show parabolicCocycles N n ≤ cocycles₁ (gammaOneRep N n)
      from inf_le_left)
  exact FiniteDimensional.of_injective ι (Submodule.inclusion_injective _)

theorem finiteDimensional_parabolicH1 (N n : ℕ) [NeZero N] :
    FiniteDimensional ℂ (ParabolicH1 N n) := by
  have := finiteDimensional_parabolicCocycles N n
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

theorem gammaOneT_fixes_infty (N : ℕ) :
    cuspAct (gammaOneT N).val OnePoint.infty = OnePoint.infty :=
  OnePoint.smul_infty_eq_self_iff.mpr rfl

/-- The principal cocycle attached to a coefficient vector. -/
def principalParabolic (N n : ℕ) (P : gammaOneRep N n) : parabolicCocycles N n :=
  ⟨d₀₁ (gammaOneRep N n) P,
    coboundaries_le_parabolicCocycles N n ⟨P, rfl⟩⟩

@[simp] theorem principalParabolic_apply (N n : ℕ) (P : gammaOneRep N n)
    (g : CongruenceSubgroup.Gamma1 N) :
    (principalParabolic N n P).val g = (gammaOneRep N n).ρ g P - P := rfl

theorem principalParabolic_mem (N n : ℕ) (P : gammaOneRep N n) :
    principalParabolic N n P ∈ parabolicCoboundaries N n :=
  (mem_parabolicCoboundaries_iff _).mpr ⟨P, fun _ => rfl⟩

theorem mem_normalizedParabolic_iff {N n : ℕ} (c : parabolicCocycles N n) :
    c ∈ normalizedParabolic N n ↔ c.val (gammaOneT N) = 0 := Iff.rfl

theorem exists_normalizedParabolic {N n : ℕ} (c : parabolicCocycles N n) :
    ∃ P : gammaOneRep N n, c - principalParabolic N n P ∈ normalizedParabolic N n := by
  obtain ⟨P, hP⟩ := ((mem_parabolicCocycles_iff _).mp c.property).2 OnePoint.infty
    (gammaOneT N) (gammaOneT_fixes_infty N)
  refine ⟨P, ?_⟩
  change c.val (gammaOneT N) - ((gammaOneRep N n).ρ (gammaOneT N) P - P) = 0
  exact sub_eq_zero.mpr hP

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

/-! # The kernel of translation normalization at arbitrary positive level -/

noncomputable section

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

def normalizedXPowerCoboundary (N n : ℕ) : normalizedParabolic N n :=
  ⟨principalParabolic N n (xPowerAtLevel N n), by
    change (gammaOneRep N n).ρ (gammaOneT N) (xPowerAtLevel N n) - xPowerAtLevel N n = 0
    rw [xPowerAtLevel_T_invariant, sub_self]⟩

theorem normalizedXPowerCoboundary_mem_ker (N n : ℕ) :
    normalizedXPowerCoboundary N n ∈ (normalizedToH1 N n).ker := by
  change (parabolicCoboundaries N n).mkQ (principalParabolic N n (xPowerAtLevel N n)) = 0
  apply (LinearMap.mem_ker).mp
  rw [Submodule.ker_mkQ]
  exact principalParabolic_mem N n (xPowerAtLevel N n)

theorem normalizedXPowerCoboundary_ne_zero {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    normalizedXPowerCoboundary N n ≠ 0 := by
  intro h
  have heq := congrArg
    (fun c : normalizedParabolic N n => (c.val.val (gammaOneLower N)).val) h
  change act !![1, 0; (N : ℤ), 1] (X 0 ^ n : Binary ℂ) - X 0 ^ n = 0 at heq
  have hev := congrArg (MvPolynomial.eval ![(0 : ℂ), 1]) heq
  simp only [MvPolynomial.eval_sub, eval_act] at hev
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hn0 := Nat.ne_of_gt hn
  simp [hn0, hN0] at hev

theorem normalizedToH1_ker_eq_span (N n : ℕ) :
    (normalizedToH1 N n).ker =
      Submodule.span ℂ {normalizedXPowerCoboundary N n} := by
  ext c
  constructor
  · intro hc
    have hc' : c.val ∈ parabolicCoboundaries N n := by
      change (parabolicCoboundaries N n).mkQ c.val = 0 at hc
      simpa only [← LinearMap.mem_ker, Submodule.ker_mkQ] using hc
    obtain ⟨P, hP⟩ := (mem_parabolicCoboundaries_iff c.val).mp hc'
    have hT : act ModularGroup.T.val P.val = P.val := by
      have h := hP (gammaOneT N)
      have hz : c.val.val (gammaOneT N) = 0 := c.property
      rw [hz] at h
      exact congrArg Subtype.val (sub_eq_zero.mp h.symm)
    have hx : P = MvPolynomial.eval ![1, 0] P.val • xPowerAtLevel N n :=
      Subtype.ext (T_invariant_eq_smul_xPower P hT)
    rw [Submodule.mem_span_singleton]
    refine ⟨MvPolynomial.eval ![1, 0] P.val, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change MvPolynomial.eval ![1, 0] P.val •
      ((gammaOneRep N n).ρ g (xPowerAtLevel N n) - xPowerAtLevel N n) = c.val.val g
    rw [hP g]
    conv_rhs => rw [hx]
    rw [map_smul, smul_sub]
  · intro hc
    exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
      (normalizedXPowerCoboundary_mem_ker N n)) hc

theorem normalizedToH1_ker_finrank {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    Module.finrank ℂ (normalizedToH1 N n).ker = 1 := by
  rw [normalizedToH1_ker_eq_span]
  exact finrank_span_singleton (K := ℂ) (v := normalizedXPowerCoboundary N n)
    (normalizedXPowerCoboundary_ne_zero hN hn)

theorem normalization_dimension_formula {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    Module.finrank ℂ (normalizedParabolic N n) = Module.finrank ℂ (ParabolicH1 N n) + 1 := by
  have : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have := finiteDimensional_parabolicCocycles N n
  have h := LinearMap.finrank_range_add_finrank_ker
    (K := ℂ) (V := normalizedParabolic N n) (V₂ := ParabolicH1 N n) (normalizedToH1 N n)
  rw [LinearMap.range_eq_top.mpr (normalizedToH1_surjective N n), finrank_top,
    normalizedToH1_ker_finrank hN hn] at h
  exact h.symm

end MTT.Cohomology
end

/-- Translation normalization adds one dimension in positive level and degree. -/
theorem solution {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    Module.finrank ℂ (MTT.Cohomology.normalizedParabolic N n) =
      Module.finrank ℂ (MTT.Cohomology.ParabolicH1 N n) + 1 :=
  MTT.Cohomology.normalization_dimension_formula hN hn
