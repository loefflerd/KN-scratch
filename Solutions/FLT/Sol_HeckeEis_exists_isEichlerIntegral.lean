import Mathlib
import Definitions.FLT.Def_HeckeEis_BinaryFormRep
import Definitions.FLT.Def_Gamma0CoeffCohomology
import Definitions.FLT.Def_HeckeEis_EichlerIntegral
import Theorems.FLT.Thm_Complex_exists_hasDerivAt_of_starConvex
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_exists_isEichlerIntegral

set_option autoImplicit false

open scoped Manifold MatrixGroups

noncomputable section

namespace HeckeEis
p2m_export "HeckeEis" "BinaryForm isHomogeneous_linePow linePow coe_linePow IsEichlerIntegral"
p2m_open "HeckeEis"

open UpperHalfPlane MvPolynomial
open scoped Manifold Polynomial

namespace EichlerIntegralExistence

variable (n : ℕ)

def degExps : Finset (Fin 2 →₀ ℕ) :=
  (Finset.range (n + 1)).image fun k => Finsupp.single 0 k + Finsupp.single 1 (n - k)

theorem mem_degExps_iff (d : Fin 2 →₀ ℕ) : d ∈ degExps n ↔ d.degree = n := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  simp only [degExps, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    simp
    omega
  · intro h
    refine ⟨d 0, by omega, ?_⟩
    ext i
    fin_cases i
    · simp
    · simp
      omega

def linePowPoly : MvPolynomial (Fin 2) ℂ[X] :=
  (C Polynomial.X * X 0 + X 1) ^ n

theorem coeff_linePow_eq_eval (d : Fin 2 →₀ ℕ) (z : ℂ) :
    AddMonoidAlgebra.coeff ((C z * X 0 + X 1 : MvPolynomial (Fin 2) ℂ) ^ n) d
      = Polynomial.eval z (AddMonoidAlgebra.coeff (linePowPoly n) d) := by
  have h : ((C z * X 0 + X 1 : MvPolynomial (Fin 2) ℂ) ^ n)
      = MvPolynomial.map (Polynomial.evalRingHom z) (linePowPoly n) := by
    simp [linePowPoly, MvPolynomial.map_X, MvPolynomial.map_C]
  rw [h, MvPolynomial.coeff_map]
  rfl

def assemble (g : (Fin 2 →₀ ℕ) → ℂ → ℂ) (τ : ℍ) : ↥(BinaryForm ℂ n) :=
  ⟨∑ d ∈ degExps n, monomial d (g d (τ : ℂ)), Submodule.sum_mem _ fun d hd =>
    (mem_homogeneousSubmodule n _).mpr (isHomogeneous_monomial _ ((mem_degExps_iff n d).mp hd))⟩

theorem coeff_assemble (g : (Fin 2 →₀ ℕ) → ℂ → ℂ) (τ : ℍ) (d : Fin 2 →₀ ℕ) :
    AddMonoidAlgebra.coeff (assemble n g τ : MvPolynomial (Fin 2) ℂ) d = if d ∈ degExps n then g d (τ : ℂ) else 0 := by
  show AddMonoidAlgebra.coeff (∑ e ∈ degExps n, monomial e (g e (τ : ℂ))) d = _
  simp only [coeff_sum, coeff_monomial, Finset.sum_ite_eq']

end EichlerIntegralExistence

end HeckeEis

open _root_.HeckeEis _root_.P2MW.S_HeckeEis_exists_isEichlerIntegral.HeckeEis HeckeEis.EichlerIntegralExistence UpperHalfPlane MvPolynomial in
theorem solution (n : ℕ) {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    ∃ F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n), HeckeEis.IsEichlerIntegral n f F := by
  let U : Set ℂ := {z | 0 < z.im}
  have hU : IsOpen U := isOpen_upperHalfPlaneSet
  have hI : ((I : ℍ) : ℂ) ∈ U := (I : ℍ).im_pos
  have hstar : StarConvex ℝ ((I : ℍ) : ℂ) U := (convex_halfSpace_im_gt 0).starConvex hI
  have hfd : DifferentiableOn ℂ (f ∘ ofComplex) U := UpperHalfPlane.mdifferentiable_iff.mp hf
  have key : ∀ d : Fin 2 →₀ ℕ, ∃ g : ℂ → ℂ, ∀ z ∈ U,
      HasDerivAt g ((f ∘ ofComplex) z * (AddMonoidAlgebra.coeff (linePowPoly n) d).eval z) z := by
    intro d
    obtain ⟨g, -, hg⟩ := Complex.exists_hasDerivAt_of_starConvex hU hI hstar
      (hfd.mul (Polynomial.differentiable _).differentiableOn)
    exact ⟨g, hg⟩
  choose g hg using key
  refine ⟨assemble n g, fun d τ => ?_⟩
  simp only [coeff_assemble]
  by_cases hd : d ∈ degExps n
  · simp only [ite_eq_left hd]
    have h2 : (f ∘ ofComplex) (τ : ℂ) * (AddMonoidAlgebra.coeff (linePowPoly n) d).eval (τ : ℂ)
        = f τ * AddMonoidAlgebra.coeff ((linePow n (τ : ℂ) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ) d := by
      rw [Function.comp_apply, ofComplex_apply, coe_linePow, coeff_linePow_eq_eval]
    rw [← h2]
    refine (hg d (τ : ℂ) τ.im_pos).congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds τ.im_pos] with z hz
    rw [ofComplex_apply_of_im_pos hz]
  · simp only [ite_eq_right hd]
    have h0 : AddMonoidAlgebra.coeff ((linePow n (τ : ℂ) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ) d = 0 :=
      (isHomogeneous_linePow n τ).coeff_eq_zero (by rwa [mem_degExps_iff] at hd)
    rw [h0, mul_zero]
    exact hasDerivAt_const _ _

end

end S_HeckeEis_exists_isEichlerIntegral
end P2MW
export P2MW.S_HeckeEis_exists_isEichlerIntegral (solution)
