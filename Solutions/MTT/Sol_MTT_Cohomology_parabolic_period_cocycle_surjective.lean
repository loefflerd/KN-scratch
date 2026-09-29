import Definitions.MTT.Def_MTT_ParabolicCohomology
import Theorems.MTT.Thm_MTT_Cohomology_integration_map
import Theorems.MTT.Thm_MTT_Cohomology_parabolicH1_finiteDimensional
import Theorems.MTT.Thm_MTT_Cohomology_parabolicH1_finrank_le
import Definitions.MTT.Def_MTT_Cohomology_Integration
import Definitions.MTT.Def_MTT_Cohomology
import Theorems.MTT.Thm_MTT_Cohomology_reflection_class
import Theorems.MTT.Thm_MTT_Cohomology_period_cocycle_injective
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false

section
/-!
# Identifying the normalized integral class

Extracted from our accepted Hecke-equivariance proof, submission
409661e4-aebb-482e-a7ec-21de19561db6. No analytic input is used here.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MTT.Cohomology
namespace MTT.IntegralClass

private lemma coeff_cusp_period_polynomial {N k : ℕ} (hk : 2 ≤ k)
    (f : CuspForm (GammaOne N) (k : ℤ)) (r : ℚ) {j : ℕ} (hj : j ≤ k - 2) :
    AddMonoidAlgebra.coeff (cuspPeriodPolynomial f r) (binaryExponent (k - 2) j) =
      ((k - 2).choose j : ℂ) * modularIntegral f (Polynomial.X ^ j) r := by
  rw [cuspPeriodPolynomial, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [ite_eq_right]
    intro h
    exact hij (by simpa [binaryExponent] using congrArg (fun v => v 0) h)
  · intro hj'
    exact absurd (Finset.mem_range.mpr (by omega)) hj'

private lemma cusp_period_polynomial_mem_sym {N k : ℕ} (hk : 2 ≤ k)
    (f : CuspForm (GammaOne N) (k : ℤ)) (r : ℚ) :
    cuspPeriodPolynomial f r ∈ MTT.Cohomology.Sym ℂ (k - 2) := by
  unfold cuspPeriodPolynomial
  refine Submodule.sum_mem _ fun j hj => ?_
  rw [MvPolynomial.mem_homogeneousSubmodule]
  apply MvPolynomial.isHomogeneous_monomial
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  have := Finset.mem_range.mp hj
  simp [binaryExponent]
  omega

private lemma sym_ext {n : ℕ} {P Q : Binary ℂ}
    (hP : P ∈ MTT.Cohomology.Sym ℂ n) (hQ : Q ∈ MTT.Cohomology.Sym ℂ n)
    (h : ∀ j ≤ n, AddMonoidAlgebra.coeff P (binaryExponent n j) =
      AddMonoidAlgebra.coeff Q (binaryExponent n j)) : P = Q := by
  rw [MvPolynomial.mem_homogeneousSubmodule] at hP hQ
  ext m
  by_cases hm : AddMonoidAlgebra.coeff P m = 0 ∧ AddMonoidAlgebra.coeff Q m = 0
  · rw [hm.1, hm.2]
  · have hdeg : m.degree = n := by
      rw [Finsupp.degree_eq_weight_one]
      rcases not_and_or.mp hm with h1 | h1
      · exact hP h1
      · exact hQ h1
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdeg
    have hm' : m = binaryExponent n (m 0) := by
      ext i
      fin_cases i <;> simp [binaryExponent]
      omega
    rw [hm']
    exact h (m 0) (by omega)

theorem val_eq_integrationCochain {N k : ℕ} (hk : 2 ≤ k)
    (f : CuspForm (GammaOne N) (k : ℤ)) (φ : Hc N (k - 2) ℂ)
    (hφ : IntegralClass f φ) : φ.val = integrationCochain f := by
  obtain ⟨hsym, hcocy, -⟩ := φ.2
  have hval (x : Cusp) : φ.val (OnePoint.infty, x) = cuspPrimitive f x := by
    rcases x with _ | r
    · exact add_eq_left.mp (hcocy OnePoint.infty OnePoint.infty OnePoint.infty)
    · apply sym_ext (hsym _ _) (cusp_period_polynomial_mem_sym hk f r)
      intro j hj
      change evaluation j r φ = _
      rw [hφ j r hj, coeff_cusp_period_polynomial hk f r hj]
  funext D
  have h := hcocy OnePoint.infty D.1 D.2
  rw [hval, hval] at h
  exact eq_sub_of_add_eq' h

end MTT.IntegralClass
end
end

section
/-!
# The group cocycle attached to a modular symbol

The base cusp is arbitrary. The cocycle is principal on each cusp stabilizer.
-/

set_option autoImplicit false
noncomputable section
namespace MTT.Cohomology

theorem modularSymbol_groupCocycle {N n : ℕ} {R : Type*} [CommRing R]
    (φ : Hc N n R) (b : Cusp) (γ δ : CongruenceSubgroup.Gamma1 N) :
    φ.val (b, cuspAct (γ * δ).val b) =
      φ.val (b, cuspAct γ.val b) + act γ.val.val (φ.val (b, cuspAct δ.val b)) := by
  have hact : cuspAct (γ * δ).val b = cuspAct γ.val (cuspAct δ.val b) := by
    simp only [cuspAct, Subgroup.coe_mul, map_mul, mul_smul]
  rw [hact, ← φ.2.2.1 b (cuspAct γ.val b), φ.2.2.2 γ]

theorem modularSymbol_cuspStabilizer {N n : ℕ} {R : Type*} [CommRing R]
    (φ : Hc N n R) (b x : Cusp) (γ : CongruenceSubgroup.Gamma1 N)
    (hx : cuspAct γ.val x = x) :
    φ.val (b, cuspAct γ.val b) = act γ.val.val (φ.val (x, b)) - φ.val (x, b) := by
  have h := φ.2.2.1 x b (cuspAct γ.val b)
  have heq := φ.2.2.2 γ x b
  rw [hx] at heq
  rw [heq] at h
  exact eq_sub_of_add_eq' h

end MTT.Cohomology
end
end

section
/-!
# The MTT period map into parabolic cohomology

The cocycle attached to a modular symbol is evaluated at (infinity, gamma infinity).
Its principal restriction at a fixed cusp has the explicit witness phi(x, infinity).
Passing to the quotient gives the ordinary Eichler–Shimura period map. No
injectivity or surjectivity is assumed in its construction.
-/

noncomputable section

namespace MTT.Cohomology

private theorem reflection_mem {N n : ℕ} (φ : Hc N n ℂ) :
    reflection φ.val ∈ Hc N n ℂ := by
  obtain ⟨ψ, hψ⟩ := (reflection_class φ).1
  rw [← hψ]
  exact ψ.property

/-- Reflection as a linear endomorphism of the modular-symbol space. -/
def reflectionLinearMap (N n : ℕ) : Hc N n ℂ →ₗ[ℂ] Hc N n ℂ where
  toFun φ := ⟨reflection φ.val, reflection_mem φ⟩
  map_add' φ ψ := by
    apply Subtype.ext
    funext D
    exact map_add _ _ _
  map_smul' a φ := by
    apply Subtype.ext
    funext D
    change act (R := ℂ) !![-1, 0; 0, 1] (a • _) = _
    exact map_smul (act (R := ℂ) !![-1, 0; 0, 1]) a _

private theorem symbol_cocycle_mem {N n : ℕ} (φ : Hc N n ℂ) :
    (fun γ : CongruenceSubgroup.Gamma1 N =>
      (⟨φ.val (OnePoint.infty, cuspAct γ.val OnePoint.infty), φ.property.1 _ _⟩ :
        gammaOneRep N n)) ∈ parabolicCocycles N n := by
  apply (mem_parabolicCocycles_iff _).mpr
  constructor
  · intro γ δ
    apply Subtype.ext
    exact (modularSymbol_groupCocycle φ OnePoint.infty γ δ).trans (add_comm _ _)
  · intro x γ hx
    refine ⟨⟨φ.val (x, OnePoint.infty), φ.property.1 _ _⟩, ?_⟩
    apply Subtype.ext
    exact modularSymbol_cuspStabilizer φ OnePoint.infty x γ hx

/-- Evaluation of a modular symbol gives a parabolic group cocycle. -/
def symbolToParabolicCocycle (N n : ℕ) : Hc N n ℂ →ₗ[ℂ] parabolicCocycles N n where
  toFun φ := ⟨fun γ => ⟨φ.val (OnePoint.infty, cuspAct γ.val OnePoint.infty),
    φ.property.1 _ _⟩, symbol_cocycle_mem φ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The sum of the holomorphic and reflected period cocycles. -/
def eichlerShimuraCocycle {N k : ℕ}
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k - 2) ℂ) :
    (CuspForm (MTT.GammaOne N) (k : ℤ) × CuspForm (MTT.GammaOne N) (k : ℤ)) →ₗ[ℂ]
      parabolicCocycles N (k - 2) :=
  (symbolToParabolicCocycle N (k - 2)).comp
    (I.comp (LinearMap.fst ℂ _ _) +
      (reflectionLinearMap N (k - 2)).comp (I.comp (LinearMap.snd ℂ _ _)))

/-- The Eichler–Shimura map into the quotient by principal cocycles. -/
def eichlerShimuraMap {N k : ℕ}
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k - 2) ℂ) :
    (CuspForm (MTT.GammaOne N) (k : ℤ) × CuspForm (MTT.GammaOne N) (k : ℤ)) →ₗ[ℂ]
      ParabolicH1 N (k - 2) :=
  (parabolicCoboundaries N (k - 2)).mkQ.comp (eichlerShimuraCocycle I)

theorem eichlerShimuraCocycle_apply {N k : ℕ} (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k - 2) ℂ)
    (hI : ∀ f, IntegralClass f (I f))
    (f : CuspForm (MTT.GammaOne N) (k : ℤ) × CuspForm (MTT.GammaOne N) (k : ℤ))
    (γ : CongruenceSubgroup.Gamma1 N) :
    ((eichlerShimuraCocycle I f).val γ).val =
      cuspPrimitive f.1 (cuspAct γ.val OnePoint.infty) +
        act !![-1, 0; 0, 1] (cuspPrimitive f.2
          (fractional !![-1, 0; 0, 1] (cuspAct γ.val OnePoint.infty))) := by
  change (I f.1).val _ + reflection (I f.2).val _ = _
  rw [MTT.IntegralClass.val_eq_integrationCochain hk _ _ (hI f.1),
    MTT.IntegralClass.val_eq_integrationCochain hk _ _ (hI f.2)]
  have hrho : fractional !![-1, 0; 0, 1] OnePoint.infty = OnePoint.infty := rfl
  have hz (g : CuspForm (MTT.GammaOne N) (k : ℤ)) : cuspPrimitive g OnePoint.infty = 0 := rfl
  simp only [reflection, integrationCochain, hrho, hz, sub_zero]

end MTT.Cohomology
end
end

section
/-!
# Surjectivity from the parabolic-cohomology dimension bound

The period-cocycle injectivity theorem remains an explicit platform dependency.
Finite-dimensionality of the parabolic target is proved independently. The
remaining dimension inequality is the Riemann–Roch/group-cohomology input in
the proof of Eichler–Shimura, not an assumed surjectivity assertion.
-/

noncomputable section

namespace MTT.Cohomology

theorem eichlerShimuraMap_injective {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k - 2) ℂ)
    (hI : ∀ f, IntegralClass f (I f)) : Function.Injective (eichlerShimuraMap I) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro f hf
  change eichlerShimuraCocycle I f ∈
    LinearMap.ker (parabolicCoboundaries N (k - 2)).mkQ at hf
  rw [Submodule.ker_mkQ] at hf
  obtain ⟨P, hP⟩ := (mem_parabolicCoboundaries_iff _).mp hf
  have hc γ := congrArg Subtype.val (hP γ)
  simp only [eichlerShimuraCocycle_apply hk I hI] at hc
  obtain ⟨hg, hh⟩ := period_cocycle_injective hN hk f.1 f.2 P.val P.property hc
  exact Prod.ext hg hh

theorem eichlerShimuraMap_surjective_of_finrank_le {N k : ℕ}
    (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k - 2) ℂ)
    (hI : ∀ f, IntegralClass f (I f))
    (hdim : Module.finrank ℂ (ParabolicH1 N (k - 2)) ≤
      2 * Module.finrank ℂ (CuspForm (MTT.GammaOne N) (k : ℤ))) :
    Function.Surjective (eichlerShimuraMap I) := by
  have : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have := parabolicH1_finiteDimensional (n := k - 2) hN
  have hinj := eichlerShimuraMap_injective hN hk I hI
  have := FiniteDimensional.of_injective (eichlerShimuraMap I) hinj
  have : FiniteDimensional ℂ (CuspForm (MTT.GammaOne N) (k : ℤ)) :=
    FiniteDimensional.of_injective
      (LinearMap.inl ℂ (CuspForm (MTT.GammaOne N) (k : ℤ))
        (CuspForm (MTT.GammaOne N) (k : ℤ))) LinearMap.inl_injective
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank _).mp hinj
  apply le_antisymm (LinearMap.finrank_le_finrank_of_injective hinj)
  simpa only [Module.finrank_prod, two_mul] using hdim

theorem parabolic_period_cocycle_surjective_of_finrank_le {N k : ℕ}
    (hN : 0 < N) (hk : 2 ≤ k)
    (I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k - 2) ℂ)
    (hI : ∀ f, IntegralClass f (I f))
    (hdim : Module.finrank ℂ (ParabolicH1 N (k - 2)) ≤
      2 * Module.finrank ℂ (CuspForm (MTT.GammaOne N) (k : ℤ)))
    (c : CongruenceSubgroup.Gamma1 N → Binary ℂ)
    (hsym : ∀ γ, c γ ∈ Sym ℂ (k - 2))
    (hcoc : ∀ γ δ, c (γ * δ) = c γ + act γ.val.val (c δ))
    (hpar : ∀ (x : Cusp) (γ : CongruenceSubgroup.Gamma1 N), cuspAct γ.val x = x →
      ∃ Q : Binary ℂ, Q ∈ Sym ℂ (k - 2) ∧ c γ = act γ.val.val Q - Q) :
    ∃ (g h : CuspForm (MTT.GammaOne N) (k : ℤ)) (P : Binary ℂ),
      P ∈ Sym ℂ (k - 2) ∧ ∀ γ : CongruenceSubgroup.Gamma1 N,
        c γ = cuspPrimitive g (cuspAct γ.val OnePoint.infty) +
          act !![-1, 0; 0, 1] (cuspPrimitive h
            (fractional !![-1, 0; 0, 1] (cuspAct γ.val OnePoint.infty))) +
          (act γ.val.val P - P) := by
  let z : parabolicCocycles N (k - 2) := ⟨fun γ => ⟨c γ, hsym γ⟩, by
    apply (mem_parabolicCocycles_iff _).mpr
    constructor
    · intro γ δ
      exact Subtype.ext ((hcoc γ δ).trans (add_comm _ _))
    · intro x γ hx
      obtain ⟨Q, hQ, heq⟩ := hpar x γ hx
      exact ⟨⟨Q, hQ⟩, Subtype.ext heq⟩⟩
  obtain ⟨f, hf⟩ := eichlerShimuraMap_surjective_of_finrank_le hN hk I hI hdim
    ((parabolicCoboundaries N (k - 2)).mkQ z)
  have hz : z - eichlerShimuraCocycle I f ∈ parabolicCoboundaries N (k - 2) := by
    rw [← Submodule.ker_mkQ (parabolicCoboundaries N (k - 2)), LinearMap.mem_ker, map_sub]
    change _ - eichlerShimuraMap I f = 0
    rw [hf, sub_self]
  obtain ⟨P, hP⟩ := (mem_parabolicCoboundaries_iff _).mp hz
  refine ⟨f.1, f.2, P.val, P.property, fun γ => ?_⟩
  have heq := congrArg Subtype.val (hP γ)
  change c γ - ((eichlerShimuraCocycle I f).val γ).val = act γ.val.val P.val - P.val at heq
  rw [eichlerShimuraCocycle_apply hk I hI] at heq
  exact sub_eq_iff_eq_add'.mp heq

end MTT.Cohomology
end
end

noncomputable section
open MTT.Cohomology

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (c : CongruenceSubgroup.Gamma1 N → Binary ℂ)
    (hsym : ∀ γ, c γ ∈ MTT.Cohomology.Sym ℂ (k - 2))
    (hcoc : ∀ γ δ, c (γ * δ) = c γ + act γ.val.val (c δ))
    (hpar : ∀ (x : Cusp) (γ : CongruenceSubgroup.Gamma1 N), cuspAct γ.val x = x →
      ∃ Q : Binary ℂ, Q ∈ MTT.Cohomology.Sym ℂ (k - 2) ∧ c γ = act γ.val.val Q - Q) :
    ∃ (g h : CuspForm (MTT.GammaOne N) (k : ℤ)) (P : Binary ℂ),
      P ∈ MTT.Cohomology.Sym ℂ (k - 2) ∧ ∀ γ : CongruenceSubgroup.Gamma1 N,
        c γ = cuspPrimitive g (cuspAct γ.val OnePoint.infty) +
          act !![-1, 0; 0, 1] (cuspPrimitive h
            (fractional !![-1, 0; 0, 1] (cuspAct γ.val OnePoint.infty))) +
          (act γ.val.val P - P) := by
  obtain ⟨I, _, _, hI⟩ := MTT.Cohomology.integration_map hN hk
  exact MTT.Cohomology.parabolic_period_cocycle_surjective_of_finrank_le hN hk I hI
    (MTT.Cohomology.parabolicH1_finrank_le hN hk) c hsym hcoc hpar
