import Mathlib.RepresentationTheory.Coinduced
import Mathlib.GroupTheory.Complement
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Tactic.Group
import Definitions.MTT.Def_MTT_ParabolicCohomology
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false

universe u

/-! # Finite-coset coordinates for coinduced coefficients

Restriction to a right transversal is a linear equivalence. This gives a
finite coefficient space for the general-level MTT dimension argument, without
assuming that Shapiro's isomorphism preserves parabolic restrictions.
-/

noncomputable section

namespace Rep

variable {K G : Type*} [Field K] [Group G] {H : Subgroup G} {T : Set G}

def coindCoordinates (A : Rep K H) (hT : Subgroup.IsComplement (H : Set G) T) :
    Rep.coind H.subtype A ≃ₗ[K] (T → A) where
  toFun f t := f.val t.val
  invFun v := ⟨fun x => A.ρ (hT.equiv x).1 (v (hT.equiv x).2), by
    intro h x
    change A.ρ (hT.equiv (h.val * x)).1 (v (hT.equiv (h.val * x)).2) = _
    rw [hT.equiv_mul_left h x]
    exact congrArg (fun f : Module.End K A => f (v (hT.equiv x).2))
      (A.ρ.map_mul h (hT.equiv x).1)⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    have hx := f.property (hT.equiv x).1 (hT.equiv x).2
    simpa only [Subgroup.coe_subtype, hT.equiv_fst_mul_equiv_snd] using hx.symm
  right_inv v := by
    funext t
    have ht : hT.equiv t.val = (1, t) := by
      apply hT.equiv.symm.injective
      rw [Equiv.symm_apply_apply]
      change t.val = (1 : H).val * t.val
      simp
    change A.ρ (hT.equiv t.val).1 (v (hT.equiv t.val).2) = v t
    rw [ht]
    exact congrArg (fun f : Module.End K A => f (v t)) A.ρ.map_one
  map_add' f g := rfl
  map_smul' a f := rfl

end Rep

/-! # Explicit degree-one Shapiro cocycles

The lift is the usual transversal construction, written as a difference of
cocycle values. Compare the proved platform lifting theorem
99ca3e82-c9c6-5732-8f47-c7035a0102ff, proof
4daf947c-3676-51e9-8e78-97c720db5c26. Only the ordinary algebraic construction
is used here; no continuity or Galois-level condition is needed for MTT.
-/

noncomputable section

namespace groupCohomology

variable {K G : Type u} [Field K] [Group G] {H : Subgroup G} {T : Set G}

def coindRetraction (hT : Subgroup.IsComplement (H : Set G) T) (x : G) : H :=
  (hT.equiv x).1

theorem coindRetraction_mul (hT : Subgroup.IsComplement (H : Set G) T) (h : H) (x : G) :
    coindRetraction hT (h.val * x) = h * coindRetraction hT x :=
  congrArg Prod.fst (hT.equiv_mul_left h x)

theorem coindRetraction_mem (hT : Subgroup.IsComplement (H : Set G) T)
    (h1 : 1 ∈ T) (h : H) : coindRetraction hT h.val = h :=
  hT.equiv_fst_eq_self_of_mem_of_one_mem h1 h.property

theorem coindRetraction_transversal (hT : Subgroup.IsComplement (H : Set G) T) (t : T) :
    coindRetraction hT t.val = 1 :=
  hT.equiv_fst_eq_one_of_mem_of_one_mem H.one_mem t.property

def coindLiftValue (A : Rep.{u} K H) (hT : Subgroup.IsComplement (H : Set G) T)
    (b : cocycles₁ A) (g : G) : Rep.coind H.subtype A :=
  ⟨fun x => b (coindRetraction hT (x * g)) - b (coindRetraction hT x), by
    intro h x
    change b (coindRetraction hT (h.val * x * g)) - b (coindRetraction hT (h.val * x)) = _
    rw [mul_assoc, coindRetraction_mul, coindRetraction_mul]
    have hb (s t : H) : b (s * t) = A.ρ s (b t) + b s :=
      (mem_cocycles₁_iff _).mp b.property s t
    rw [hb, hb, map_sub]
    abel⟩

def coindCocycleLift (A : Rep.{u} K H) (hT : Subgroup.IsComplement (H : Set G) T)
    (b : cocycles₁ A) : cocycles₁ (Rep.coind H.subtype A) :=
  ⟨coindLiftValue A hT b, (mem_cocycles₁_iff _).mpr (by
    intro g h
    apply Subtype.ext
    funext x
    change b (coindRetraction hT (x * (g * h))) - b (coindRetraction hT x) =
      (b (coindRetraction hT (x * g * h)) - b (coindRetraction hT (x * g))) +
        (b (coindRetraction hT (x * g)) - b (coindRetraction hT x))
    rw [mul_assoc]
    abel)⟩

theorem coindCocycleLift_eval_one (A : Rep.{u} K H)
    (hT : Subgroup.IsComplement (H : Set G) T) (h1 : 1 ∈ T)
    (b : cocycles₁ A) (h : H) : (coindCocycleLift A hT b h.val).val 1 = b h := by
  change b (coindRetraction hT (1 * h.val)) - b (coindRetraction hT 1) = b h
  have hOne : coindRetraction hT (1 : G) = 1 := coindRetraction_mem hT h1 (1 : H)
  rw [one_mul, coindRetraction_mem hT h1 h, hOne, cocycles₁_map_one, sub_zero]

end groupCohomology

/-! # Detecting cyclic principality on a positive power

Over characteristic zero, a cocycle is principal on a cyclic subgroup as soon
as it is principal on a finite-index subgroup of that cyclic subgroup. Passing
to coinvariants makes the cocycle's value on the m-th power equal to m times
its value on the generator.
-/

noncomputable section

namespace groupCohomology

variable {K G : Type u} [Field K] [CharZero K] [Group G] {A : Rep.{u} K G}

theorem cocycle_mem_range_of_pow (c : cocycles₁ A) (g : G) {m : ℕ} (hm : 0 < m)
    (hc : c (g ^ m) ∈ LinearMap.range (A.ρ (g ^ m) - LinearMap.id)) :
    c g ∈ LinearMap.range (A.ρ g - LinearMap.id) := by
  let R := LinearMap.range (A.ρ g - LinearMap.id)
  let q := R.mkQ
  have hq (v : A) : q (A.ρ g v) = q v := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply LinearMap.mem_ker.mp
    rw [Submodule.ker_mkQ]
    exact ⟨v, rfl⟩
  have hpow (j : ℕ) (v : A) : q (A.ρ (g ^ j) v) = q v := by
    induction j generalizing v with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, map_mul, Module.End.mul_apply]
      exact (ih (A.ρ g v)).trans (hq v)
  have hcpow (j : ℕ) : q (c (g ^ j)) = j • q (c g) := by
    induction j with
    | zero => simp [cocycles₁_map_one]
    | succ j ih =>
      have hcj : c (g ^ j * g) = A.ρ (g ^ j) (c g) + c (g ^ j) :=
        (mem_cocycles₁_iff _).mp c.property (g ^ j) g
      rw [pow_succ, hcj, map_add, hpow, ih]
      simp [add_comm, add_nsmul]
  obtain ⟨v, hv⟩ := hc
  have hz : q (c (g ^ m)) = 0 := by
    rw [← hv]
    change q (A.ρ (g ^ m) v - v) = 0
    rw [map_sub, hpow, sub_self]
  rw [hcpow] at hz
  have hzK : (m : K) • q (c g) = 0 := by simpa only [Nat.cast_smul_eq_nsmul] using hz
  have hzero : q (c g) = 0 :=
    (smul_eq_zero.mp hzK).resolve_left (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm))
  have hmem := LinearMap.mem_ker.mpr hzero
  rwa [Submodule.ker_mkQ] at hmem

end groupCohomology

/-! # Cyclic restrictions of lifted cocycles

This is the finite-power argument in the accepted Gamma0 Shapiro proof
c7770f6c-0e05-5212-ac9a-be8ca5205c57, adapted to mathlib's coinduced module
and an arbitrary subgroup. A power fixing all cosets makes the restriction
pointwise principal; characteristic zero then descends principality to the
generator. The result will be specialized to MTT cusp stabilizers.
-/

noncomputable section

namespace groupCohomology

variable {K G : Type u} [Field K] [CharZero K] [Group G] {H : Subgroup G} {T : Set G}

theorem coindCocycleLift_mem_range (A : Rep.{u} K H)
    (hT : Subgroup.IsComplement (H : Set G) T) (b : cocycles₁ A) (g : G)
    {m : ℕ} (hm : 0 < m)
    (hmem : ∀ t : T, t.val * g ^ m * t.val⁻¹ ∈ H)
    (hpar : ∀ t : T, b ⟨t.val * g ^ m * t.val⁻¹, hmem t⟩ ∈
      LinearMap.range (A.ρ ⟨t.val * g ^ m * t.val⁻¹, hmem t⟩ - LinearMap.id)) :
    coindCocycleLift A hT b g ∈
      LinearMap.range ((Rep.coind H.subtype A).ρ g - LinearMap.id) := by
  classical
  let γ (t : T) : H := ⟨t.val * g ^ m * t.val⁻¹, hmem t⟩
  choose v hv using hpar
  let F := (Rep.coindCoordinates A hT).symm v
  apply cocycle_mem_range_of_pow (coindCocycleLift A hT b) g hm
  refine ⟨F, ?_⟩
  apply (Rep.coindCoordinates A hT).injective
  funext t
  have ht : t.val * g ^ m = (γ t).val * t.val := by simp [γ, mul_assoc]
  have hval : F.val t.val = v t :=
    congrFun ((Rep.coindCoordinates A hT).apply_symm_apply v) t
  have hpower : F.val (t.val * g ^ m) = A.ρ (γ t) (v t) := by
    rw [ht]
    exact (F.property (γ t) t.val).trans (congrArg (A.ρ (γ t)) hval)
  change F.val (t.val * g ^ m) - F.val t.val =
    b (coindRetraction hT (t.val * g ^ m)) - b (coindRetraction hT t.val)
  rw [hpower, hval, ht, coindRetraction_mul, coindRetraction_transversal, mul_one,
    cocycles₁_map_one, sub_zero]
  exact hv t

end groupCohomology

/-! # Parabolic Shapiro lifting for Gamma1(N)

A power in the principal congruence subgroup fixes every right coset.
Its conjugates preserve rational cusps, so pointwise parabolic principality
and characteristic-zero power restriction prove the lifted cocycle parabolic.
-/

noncomputable section

namespace MTT.Cohomology

open groupCohomology Matrix

theorem coindCocycleLift_parabolic {N n : ℕ} (hN : 0 < N)
    {T : Set (SpecialLinearGroup (Fin 2) ℤ)}
    (hT : Subgroup.IsComplement (CongruenceSubgroup.Gamma1 N : Set _) T)
    (b : parabolicCocycles N n) (x : Cusp) (g : SpecialLinearGroup (Fin 2) ℤ)
    (hx : cuspAct g x = x) :
    coindCocycleLift (gammaOneRep N n) hT ⟨b.val, b.property.1⟩ g ∈
      LinearMap.range
        ((Rep.coind (CongruenceSubgroup.Gamma1 N).subtype (gammaOneRep N n)).ρ g -
          LinearMap.id) := by
  have : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have : (CongruenceSubgroup.Gamma N).Normal := CongruenceSubgroup.Gamma_normal N
  let m := (CongruenceSubgroup.Gamma N).index
  have hm : 0 < m := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have hmem (t : T) : t.val * g ^ m * t.val⁻¹ ∈ CongruenceSubgroup.Gamma1 N := by
    have ht := (CongruenceSubgroup.Gamma_normal N).conj_mem
      (g ^ m) ((CongruenceSubgroup.Gamma N).pow_index_mem g) t.val
    rw [CongruenceSubgroup.Gamma_mem] at ht
    exact (CongruenceSubgroup.Gamma1_mem N _).mpr ⟨ht.1, ht.2.2.2, ht.2.2.1⟩
  apply coindCocycleLift_mem_range (gammaOneRep N n) hT ⟨b.val, b.property.1⟩ g hm hmem
  intro t
  have hx' : SpecialLinearGroup.mapGL ℚ g • x = x := hx
  have hpow (j : ℕ) : SpecialLinearGroup.mapGL ℚ (g ^ j) • x = x := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, map_mul, mul_smul, hx', ih]
  have hfix : cuspAct (t.val * g ^ m * t.val⁻¹) (cuspAct t.val x) = cuspAct t.val x := by
    simp only [cuspAct, map_mul, map_inv, mul_smul, inv_smul_smul, hpow]
  obtain ⟨P, hP⟩ := ((mem_parabolicCocycles_iff _).mp b.property).2
    (cuspAct t.val x) ⟨t.val * g ^ m * t.val⁻¹, hmem t⟩ hfix
  exact ⟨P, hP.symm⟩

theorem exists_parabolic_coinduced_cocycle {N n : ℕ} (hN : 0 < N)
    (b : parabolicCocycles N n) :
    ∃ c : cocycles₁
        (Rep.coind (CongruenceSubgroup.Gamma1 N).subtype (gammaOneRep N n)),
      (∀ h : CongruenceSubgroup.Gamma1 N, (c h.val).val 1 = b.val h) ∧
      ∀ (x : Cusp) (g : SpecialLinearGroup (Fin 2) ℤ), cuspAct g x = x →
        ∃ P : Rep.coind (CongruenceSubgroup.Gamma1 N).subtype (gammaOneRep N n),
          c g = (Rep.coind (CongruenceSubgroup.Gamma1 N).subtype
            (gammaOneRep N n)).ρ g P - P := by
  obtain ⟨T, hT, h1⟩ := (CongruenceSubgroup.Gamma1 N).exists_isComplement_right 1
  refine ⟨coindCocycleLift (gammaOneRep N n) hT ⟨b.val, b.property.1⟩,
    fun h => coindCocycleLift_eval_one _ hT h1 _ h, ?_⟩
  intro x g hx
  obtain ⟨P, hP⟩ := coindCocycleLift_parabolic hN hT b x g hx
  exact ⟨P, hP.symm⟩

end MTT.Cohomology

theorem solution {N n : ℕ} (hN : 0 < N)
    (b : MTT.Cohomology.parabolicCocycles N n) :
    ∃ c : groupCohomology.cocycles₁
        (Rep.coind (CongruenceSubgroup.Gamma1 N).subtype (MTT.Cohomology.gammaOneRep N n)),
      (∀ h : CongruenceSubgroup.Gamma1 N, (c h.val).val 1 = b.val h) ∧
      ∀ (x : MTT.Cohomology.Cusp) (g : Matrix.SpecialLinearGroup (Fin 2) ℤ),
        MTT.Cohomology.cuspAct g x = x →
        ∃ P : Rep.coind (CongruenceSubgroup.Gamma1 N).subtype (MTT.Cohomology.gammaOneRep N n),
          c g = (Rep.coind (CongruenceSubgroup.Gamma1 N).subtype
            (MTT.Cohomology.gammaOneRep N n)).ρ g P - P :=
  MTT.Cohomology.exists_parabolic_coinduced_cocycle hN b
