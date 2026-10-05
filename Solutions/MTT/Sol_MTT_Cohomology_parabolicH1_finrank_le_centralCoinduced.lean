import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

import Definitions.MTT.Def_MTT_FullParabolicCohomology
import Theorems.FLT.Thm_Rep_finiteDimensional_coind_and_finrank_coind_eq_index_mul
import Theorems.MTT.Thm_MTT_Cohomology_exists_parabolic_coinduced_cocycle

/-! # Parabolic Shapiro comparison with central-fixed coinduced coefficients -/

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

theorem centralAverage_cocycle (c : groupCohomology.cocycles₁ A) (g : G) :
    (centralAverage A z hz hz₂ (c g)).val =
      c g + (A.ρ g ((2 : ℂ)⁻¹ • c z) - (2 : ℂ)⁻¹ • c z) := by
  have hc := (groupCohomology.mem_cocycles₁_iff c).mp c.property
  have h : A.ρ z (c g) + c z = A.ρ g (c z) + c g := by
    rw [← hc, hz, hc]
  have h' : A.ρ z (c g) = A.ρ g (c z) + c g - c z :=
    eq_sub_of_add_eq h
  change (2 : ℂ)⁻¹ • (c g + A.ρ z (c g)) = _
  rw [h', map_smul]
  module

end Rep

namespace MTT.Cohomology

open groupCohomology

variable (A : Rep ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ))

def centralParabolicProjection : fullParabolicCocycles A →ₗ[ℂ]
    fullParabolicCocycles (Rep.centralFixedRep A (-1) neg_one_central) where
  toFun c := ⟨fun g => Rep.centralAverage A (-1) neg_one_central
    (by simp only [neg_mul_neg, one_mul]) (c.val g), by
    obtain ⟨hc, hp⟩ := (mem_fullParabolicCocycles_iff A c.val).mp c.property
    apply (mem_fullParabolicCocycles_iff _ _).mpr
    constructor
    · apply (mem_cocycles₁_iff _).mpr
      intro g h
      change Rep.centralAverage A (-1) neg_one_central _ (c.val (g * h)) = _
      rw [(mem_cocycles₁_iff _).mp hc, map_add, Rep.centralAverage_comm]
    · intro x g hg
      obtain ⟨P, hP⟩ := hp x g hg
      refine ⟨Rep.centralAverage A (-1) neg_one_central
        (by simp only [neg_mul_neg, one_mul]) P, ?_⟩
      change _ = Rep.centralAverage A (-1) neg_one_central _ (c.val g)
      rw [← hP]
      change _ = Rep.centralAverage A (-1) neg_one_central _ (A.ρ g P - P)
      rw [map_sub, Rep.centralAverage_comm]
      rfl⟩
  map_add' c d := by
    apply Subtype.ext
    funext g
    exact map_add _ _ _
  map_smul' a c := by
    apply Subtype.ext
    funext g
    exact map_smul _ _ _

theorem centralParabolicProjection_principal_iff (c : fullParabolicCocycles A) :
    (centralParabolicProjection A c).val ∈
        coboundaries₁ (Rep.centralFixedRep A (-1) neg_one_central) ↔
      c.val ∈ coboundaries₁ A := by
  constructor
  · rintro ⟨P, hP⟩
    let Q : A := (2 : ℂ)⁻¹ • c.val (-1)
    refine ⟨P.val - Q, funext fun g => ?_⟩
    rw [d₀₁_hom_apply]
    have hPg : A.ρ g P.val - P.val = c.val g + (A.ρ g Q - Q) := by
      have h := congrArg
        (fun f : Matrix.SpecialLinearGroup (Fin 2) ℤ →
          Rep.centralFixedRep A (-1) neg_one_central => (f g).val) hP
      change A.ρ g P.val - P.val =
        (Rep.centralAverage A (-1) neg_one_central
          (by simp only [neg_mul_neg, one_mul]) (c.val g)).val at h
      exact h.trans (Rep.centralAverage_cocycle A (-1) neg_one_central
        (by simp only [neg_mul_neg, one_mul]) ⟨c.val, c.property.1⟩ g)
    calc
      A.ρ g (P.val - Q) - (P.val - Q) =
          (A.ρ g P.val - P.val) - (A.ρ g Q - Q) := by rw [map_sub]; abel
      _ = c.val g := by rw [hPg]; abel
  · rintro ⟨P, hP⟩
    refine ⟨Rep.centralAverage A (-1) neg_one_central
      (by simp only [neg_mul_neg, one_mul]) P, funext fun g => ?_⟩
    rw [d₀₁_hom_apply]
    change _ = Rep.centralAverage A (-1) neg_one_central _ (c.val g)
    rw [← Rep.centralAverage_comm, ← map_sub]
    exact congrArg (Rep.centralAverage A (-1) neg_one_central
      (by simp only [neg_mul_neg, one_mul])) (congrFun hP g)

def centralParabolicClass : fullParabolicCocycles A →ₗ[ℂ]
    FullParabolicH1 (Rep.centralFixedRep A (-1) neg_one_central) :=
  (fullParabolicCoboundaries _).mkQ.comp (centralParabolicProjection A)

theorem centralParabolicClass_ker :
    (centralParabolicClass A).ker = fullParabolicCoboundaries A := by
  ext c
  change (fullParabolicCoboundaries _).mkQ (centralParabolicProjection A c) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact centralParabolicProjection_principal_iff A c

def centralParabolicH1 : FullParabolicH1 A →ₗ[ℂ]
    FullParabolicH1 (Rep.centralFixedRep A (-1) neg_one_central) :=
  (fullParabolicCoboundaries A).liftQ (centralParabolicClass A)
    (centralParabolicClass_ker A).ge

theorem centralParabolicH1_injective : Function.Injective (centralParabolicH1 A) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot _ _ _ (centralParabolicClass_ker A).le

theorem fullParabolicH1_finrank_le_centralFixed
    [FiniteDimensional ℂ
      (FullParabolicH1 (Rep.centralFixedRep A (-1) neg_one_central))] :
    Module.finrank ℂ (FullParabolicH1 A) ≤
      Module.finrank ℂ (FullParabolicH1 (Rep.centralFixedRep A (-1) neg_one_central)) :=
  LinearMap.finrank_le_finrank_of_injective (centralParabolicH1_injective A)

end MTT.Cohomology

section

namespace MTT.Cohomology

open groupCohomology

variable (N n : ℕ)

theorem coind_action_eval_one (h : CongruenceSubgroup.Gamma1 N)
    (P : Rep.coind (CongruenceSubgroup.Gamma1 N).subtype (gammaOneRep N n)) :
    (((Rep.coind (CongruenceSubgroup.Gamma1 N).subtype (gammaOneRep N n)).ρ h.val P).val 1) =
      (gammaOneRep N n).ρ h (P.val 1) := by
  change P.val (1 * h.val) = _
  simpa only [one_mul, mul_one, Subgroup.coe_subtype] using P.property h 1

def parabolicCoindEval :
    fullParabolicCocycles
      (Rep.coind (CongruenceSubgroup.Gamma1 N).subtype (gammaOneRep N n)) →ₗ[ℂ]
        parabolicCocycles N n where
  toFun c := ⟨fun h => (c.val h.val).val 1, by
    obtain ⟨hc, hp⟩ := (mem_fullParabolicCocycles_iff _ _).mp c.property
    apply (mem_parabolicCocycles_iff _).mpr
    constructor
    · intro g h
      have hh := congrArg
        (fun P : Rep.coind (CongruenceSubgroup.Gamma1 N).subtype (gammaOneRep N n) => P.val 1)
        ((mem_cocycles₁_iff _).mp hc g.val h.val)
      change (c.val (g * h).val).val 1 =
        (((Rep.coind (CongruenceSubgroup.Gamma1 N).subtype (gammaOneRep N n)).ρ
          g.val (c.val h.val)).val 1) + (c.val g.val).val 1 at hh
      rw [coind_action_eval_one N n g (c.val h.val)] at hh
      exact hh
    · intro x g hg
      obtain ⟨P, hP⟩ := hp x g.val hg
      refine ⟨P.val 1, ?_⟩
      have hh := congrArg
        (fun P : Rep.coind (CongruenceSubgroup.Gamma1 N).subtype (gammaOneRep N n) => P.val 1) hP
      change (((Rep.coind (CongruenceSubgroup.Gamma1 N).subtype
        (gammaOneRep N n)).ρ g.val P).val 1)
        - P.val 1 = (c.val g.val).val 1 at hh
      rw [coind_action_eval_one N n g P] at hh
      exact hh.symm⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem parabolicCoindEval_surjective (hN : 0 < N) :
    Function.Surjective (parabolicCoindEval N n) := by
  intro b
  obtain ⟨c, hc, hp⟩ := exists_parabolic_coinduced_cocycle hN b
  refine ⟨⟨c.val, (mem_fullParabolicCocycles_iff _ _).mpr ⟨c.property, ?_⟩⟩,
    Subtype.ext (funext hc)⟩
  intro x g hg
  obtain ⟨P, hP⟩ := hp x g hg
  exact ⟨P, hP.symm⟩

theorem parabolicCoindEval_maps_coboundaries :
    fullParabolicCoboundaries
        (Rep.coind (CongruenceSubgroup.Gamma1 N).subtype (gammaOneRep N n)) ≤
      (parabolicCoboundaries N n).comap (parabolicCoindEval N n) := by
  intro c hc
  change c.val ∈ coboundaries₁ _ at hc
  obtain ⟨P, hP⟩ := hc
  change (parabolicCoindEval N n c).val ∈ coboundaries₁ _
  refine ⟨P.val 1, funext fun g => ?_⟩
  rw [d₀₁_hom_apply]
  have hh := congrArg
    (fun f : Matrix.SpecialLinearGroup (Fin 2) ℤ →
      Rep.coind (CongruenceSubgroup.Gamma1 N).subtype (gammaOneRep N n) => (f g.val).val 1) hP
  change (((Rep.coind (CongruenceSubgroup.Gamma1 N).subtype (gammaOneRep N n)).ρ g.val P).val 1)
    - P.val 1 = (c.val g.val).val 1 at hh
  rw [coind_action_eval_one N n g P] at hh
  exact hh

def parabolicCoindH1Eval :
    FullParabolicH1
      (Rep.coind (CongruenceSubgroup.Gamma1 N).subtype (gammaOneRep N n)) →ₗ[ℂ]
        ParabolicH1 N n :=
  Submodule.mapQ _ _ (parabolicCoindEval N n) (parabolicCoindEval_maps_coboundaries N n)

theorem parabolicCoindH1Eval_surjective (hN : 0 < N) :
    Function.Surjective (parabolicCoindH1Eval N n) := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H b =>
      obtain ⟨c, hc⟩ := parabolicCoindEval_surjective N n hN b
      exact ⟨(fullParabolicCoboundaries _).mkQ c,
        congrArg (parabolicCoboundaries N n).mkQ hc⟩

end MTT.Cohomology

section

namespace MTT.Cohomology

theorem fullParabolicCocycles_finiteDimensional
    (A : Rep ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [FiniteDimensional ℂ A] :
    FiniteDimensional ℂ (fullParabolicCocycles A) := by
  have : Group.FG (Matrix.SpecialLinearGroup (Fin 2) ℤ) :=
    Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T},
      SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩
  have := groupCohomology.finiteDimensional_cocycles₁ (A := A)
  exact FiniteDimensional.of_injective
    (Submodule.inclusion (show fullParabolicCocycles A ≤ groupCohomology.cocycles₁ A
      from inf_le_left)) (Submodule.inclusion_injective _)

theorem parabolicH1_finrank_le_centralCoinduced_via_counit {N n : ℕ} (hN : 0 < N) :
    Module.finrank ℂ (ParabolicH1 N n) ≤
      Module.finrank ℂ (FullParabolicH1 (centralCoinduced N n)) := by
  have : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have : FiniteDimensional ℂ (gammaOneRep N n) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 2) ℂ n)
  have := (Rep.finiteDimensional_coind_and_finrank_coind_eq_index_mul
    (CongruenceSubgroup.Gamma1 N) (gammaOneRep N n)).1
  have := fullParabolicCocycles_finiteDimensional
    (Rep.coind (CongruenceSubgroup.Gamma1 N).subtype (gammaOneRep N n))
  have := fullParabolicCocycles_finiteDimensional (centralCoinduced N n)
  exact (LinearMap.finrank_le_finrank_of_surjective
    (parabolicCoindH1Eval_surjective N n hN)).trans
      (fullParabolicH1_finrank_le_centralFixed _)

end MTT.Cohomology

theorem solution {N n : ℕ} (hN : 0 < N) :
    Module.finrank ℂ (MTT.Cohomology.ParabolicH1 N n) ≤
      Module.finrank ℂ (MTT.Cohomology.FullParabolicH1
        (MTT.Cohomology.centralCoinduced N n)) :=
  MTT.Cohomology.parabolicH1_finrank_le_centralCoinduced_via_counit hN
