module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.NumberTheory.Modular

import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.GroupTheory.Complement

/-!
# Stokes' theorem on `Γ\ℍ` for an invariant `(0,1)`-form vanishing at the cusps

Let `Γ ≤ SL(2, ℤ)`, let `R` be a finite set of right-coset representatives of `Γ`, and let
`A : ℂ → ℂ` be real-`C¹` on `ℍ` with `A (γ z) = conj (c z + d) ^ 2 * A z` for `γ ∈ Γ` (so that the
`(0,1)`-form `A dz̄` is `Γ`-invariant), with all `SL(2, ℤ)`-pullbacks tending to `0` at `i∞`.
Then the sum over `g ∈ R` of the integrals of the Wirtinger derivative `∂_z A` over the tiles
`g 𝒟` vanishes.

The proof pulls every tile back to the standard truncated tile `𝒟_H`, applies Green's theorem
there (fibrewise fundamental theorem of calculus on a region between graphs), and cancels the
side and arc contributions using only the `Γ`-invariance and the permutation of `R` induced by
right multiplication with `T` and `S`; the horizontal caps vanish in the limit `H → ∞`.
(Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §8.2.)
-/

noncomputable section privateSection

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Modular

open Complex Set Filter Topology intervalIntegral ModularGroup

namespace MTT.Stokes

/-! ### The Möbius map, the automorphy denominator, pullbacks, and the tile -/

/-- The Möbius transformation of `g ∈ SL(2, ℤ)`, as a map `ℂ → ℂ`. -/
def mob (g : SL(2, ℤ)) (z : ℂ) : ℂ :=
  ((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) / ((g 1 0 : ℂ) * z + (g 1 1 : ℂ))

/-- The automorphy denominator `c z + d` of `g`, as a map `ℂ → ℂ`. -/
def den (g : SL(2, ℤ)) (z : ℂ) : ℂ := (g 1 0 : ℂ) * z + (g 1 1 : ℂ)

/-- The Wirtinger derivative `∂_z A = (∂_x A - i ∂_y A) / 2`, via the real Fréchet derivative. -/
def wirtinger (A : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ A z 1 - Complex.I * fderiv ℝ A z Complex.I)

/-- The coefficient of the pullback `g^*(A dz̄) = A (g z) * conj (g' z) dz̄`, `g' z = (c z + d)⁻²`. -/
def pull (g : SL(2, ℤ)) (A : ℂ → ℂ) (z : ℂ) : ℂ :=
  A (mob g z) * ((starRingEnd ℂ (den g z)) ^ 2)⁻¹

/-- The standard fundamental domain truncated at height `H`, as a subset of `ℂ`. -/
def tile (H : ℝ) : Set ℂ := {z | 0 ≤ z.im ∧ z.im ≤ H ∧ |z.re| ≤ 1 / 2 ∧ 1 ≤ ‖z‖}

/-- The lower boundary `x ↦ √(1 - x²)` of the standard tile. -/
def arcHeight (x : ℝ) : ℝ := Real.sqrt (1 - x ^ 2)

/-- The signed half-width `y ↦ -√(max 0 (1 - y²))` of the left half of the standard tile at
height `y`. -/
def halfWidth (y : ℝ) : ℝ := -Real.sqrt (max 0 (1 - y ^ 2))

/-! ### Basic properties of the Möbius map (T201) -/

theorem den_eq_denom (g : SL(2, ℤ)) (τ : ℍ) : den g τ = denom g τ := by
  simp [den, denom_apply]

theorem den_ne_zero (g : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : den g z ≠ 0 := by
  have h : den g z = denom g (⟨z, hz⟩ : ℍ) := den_eq_denom g ⟨z, hz⟩
  rw [h]
  exact denom_ne_zero _ _

theorem mob_eq_coe_smul (g : SL(2, ℤ)) (τ : ℍ) : mob g τ = ((g • τ : ℍ) : ℂ) := by
  rw [coe_specialLinearGroup_apply]
  simp [mob]

theorem im_mob_pos (g : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : 0 < (mob g z).im := by
  have h : mob g z = ((g • (⟨z, hz⟩ : ℍ) : ℍ) : ℂ) := mob_eq_coe_smul g ⟨z, hz⟩
  rw [h]
  exact (g • (⟨z, hz⟩ : ℍ)).im_pos

theorem hasDerivAt_mob (g : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (mob g) ((den g z ^ 2)⁻¹) z := by
  have hd : den g z ≠ 0 := den_ne_zero g hz
  have h1 : HasDerivAt (fun w : ℂ ↦ (g 0 0 : ℂ) * w + (g 0 1 : ℂ)) (g 0 0 : ℂ) z := by
    simpa using ((hasDerivAt_id z).const_mul (g 0 0 : ℂ)).add_const (g 0 1 : ℂ)
  have h2 : HasDerivAt (fun w : ℂ ↦ (g 1 0 : ℂ) * w + (g 1 1 : ℂ)) (g 1 0 : ℂ) z := by
    simpa using ((hasDerivAt_id z).const_mul (g 1 0 : ℂ)).add_const (g 1 1 : ℂ)
  have hdet : (g 0 0 : ℂ) * (g 1 1 : ℂ) - (g 0 1 : ℂ) * (g 1 0 : ℂ) = 1 := by
    have := g.det_coe
    rw [Matrix.det_fin_two] at this
    exact_mod_cast this
  refine (h1.div h2 hd).congr_deriv ?_
  simp only [den] at hd ⊢
  field_simp
  linear_combination hdet

theorem mob_mul (g h : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : mob (g * h) z = mob g (mob h z) := by
  have h1 : den h z ≠ 0 := den_ne_zero h hz
  have h2 : den g (mob h z) ≠ 0 := den_ne_zero g (im_mob_pos h hz)
  have h3 : den (g * h) z ≠ 0 := den_ne_zero (g * h) hz
  simp only [den, mob] at h1 h2 h3 ⊢
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at h3 ⊢
  push_cast at h3 ⊢
  field_simp
  ring

theorem den_mul (g h : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    den (g * h) z = den g (mob h z) * den h z := by
  have h1 : den h z ≠ 0 := den_ne_zero h hz
  simp only [den, mob] at h1 ⊢
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  field_simp
  ring

theorem pull_mul (g h : SL(2, ℤ)) (A : ℂ → ℂ) {z : ℂ} (hz : 0 < z.im) :
    pull (g * h) A z = pull h (pull g A) z := by
  simp only [pull, mob_mul g h hz, den_mul g h hz, map_mul, mul_pow, mul_inv]
  ring

theorem pull_eq_self_of_mem {Γ : Subgroup SL(2, ℤ)} {A : ℂ → ℂ}
    (hinv : ∀ γ ∈ Γ, ∀ τ : ℍ, A ((γ • τ : ℍ) : ℂ) = (starRingEnd ℂ (denom γ τ)) ^ 2 * A τ)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) {z : ℂ} (hz : 0 < z.im) : pull γ A z = A z := by
  have h1 : mob γ z = ((γ • (⟨z, hz⟩ : ℍ) : ℍ) : ℂ) := mob_eq_coe_smul γ ⟨z, hz⟩
  have h2 : den γ z = denom γ (⟨z, hz⟩ : ℍ) := den_eq_denom γ ⟨z, hz⟩
  have hd : (starRingEnd ℂ (denom γ (⟨z, hz⟩ : ℍ))) ^ 2 ≠ 0 :=
    pow_ne_zero _ ((map_ne_zero _).2 (denom_ne_zero _ _))
  rw [pull, h1, h2, hinv γ hγ ⟨z, hz⟩, mul_comm _ (A _), mul_inv_cancel_right₀ hd]

theorem mob_injOn (g : SL(2, ℤ)) : InjOn (mob g) upperHalfPlaneSet := by
  intro z hz w hw hzw
  have hz' : 0 < z.im := hz
  have hw' : 0 < w.im := hw
  have h1 : mob g z = ((g • (⟨z, hz'⟩ : ℍ) : ℍ) : ℂ) := mob_eq_coe_smul g ⟨z, hz'⟩
  have h2 : mob g w = ((g • (⟨w, hw'⟩ : ℍ) : ℍ) : ℂ) := mob_eq_coe_smul g ⟨w, hw'⟩
  rw [h1, h2] at hzw
  have h3 : (⟨z, hz'⟩ : ℍ) = ⟨w, hw'⟩ := smul_left_cancel g (UpperHalfPlane.ext hzw)
  exact congrArg UpperHalfPlane.coe h3

theorem tile_eq_coe_image (H : ℝ) :
    tile H = UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H :=
  (ModularGroup.coe_truncatedFundamentalDomain H).symm

theorem image_coe_fd_eq (g : SL(2, ℤ)) :
    (fun τ : ℍ ↦ ((g • τ : ℍ) : ℂ)) '' 𝒟 = mob g '' (UpperHalfPlane.coe '' 𝒟) := by
  rw [Set.image_image]
  exact Set.image_congr fun τ _ ↦ (mob_eq_coe_smul g τ).symm

/-! ### The Wirtinger derivative (T202) -/

theorem clm_apply_eq_re_smul_add_im_smul (L : ℂ →L[ℝ] ℂ) (w : ℂ) :
    L w = w.re • L 1 + w.im • L Complex.I := by
  have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
    rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]
  conv_lhs => rw [hw]
  rw [map_add, map_smul, map_smul]

theorem wirtinger_comp_hasDerivAt {A m : ℂ → ℂ} {z m' : ℂ} (hA : DifferentiableAt ℝ A (m z))
    (hm : HasDerivAt m m' z) : wirtinger (fun w ↦ A (m w)) z = m' * wirtinger A (m z) := by
  have hmd : DifferentiableAt ℝ m z := hm.differentiableAt.restrictScalars ℝ
  have hc : (fun w ↦ A (m w)) = A ∘ m := rfl
  rw [wirtinger, wirtinger, hc, fderiv_comp z hA hmd, hm.complexToReal_fderiv.fderiv]
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply, one_apply_eq_self, smul_eq_mul,
    mul_one]
  rw [clm_apply_eq_re_smul_add_im_smul _ m', clm_apply_eq_re_smul_add_im_smul _ (m' * Complex.I),
    mul_left_comm]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem wirtinger_mul {F G : ℂ → ℂ} {z : ℂ} (hF : DifferentiableAt ℝ F z)
    (hG : DifferentiableAt ℝ G z) :
    wirtinger (fun w ↦ F w * G w) z = F z * wirtinger G z + G z * wirtinger F z := by
  simp only [wirtinger, fderiv_fun_mul hF hG, _root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

theorem wirtinger_conj_comp {h : ℂ → ℂ} {z h' : ℂ} (hh : HasDerivAt h h' z) :
    wirtinger (fun w ↦ starRingEnd ℂ (h w)) z = 0 := by
  have hc : (fun w ↦ starRingEnd ℂ (h w)) = Complex.conjCLE ∘ h := by
    funext w
    simp
  rw [wirtinger, hc, Complex.conjCLE.comp_fderiv, hh.complexToReal_fderiv.fderiv]
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply, one_apply_eq_self, smul_eq_mul,
    mul_one, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_mul, Complex.conj_I]
  linear_combination (1 / 2 : ℂ) * starRingEnd ℂ h' * Complex.I_mul_I

theorem hasDerivAt_den (g : SL(2, ℤ)) (z : ℂ) : HasDerivAt (den g) (g 1 0 : ℂ) z := by
  change HasDerivAt (fun w ↦ (g 1 0 : ℂ) * w + (g 1 1 : ℂ)) _ z
  simpa using ((hasDerivAt_id z).const_mul (g 1 0 : ℂ)).add_const (g 1 1 : ℂ)

theorem differentiableAt_of_contDiffOn {A : ℂ → ℂ} (hA : ContDiffOn ℝ 1 A upperHalfPlaneSet)
    {z : ℂ} (hz : 0 < z.im) : DifferentiableAt ℝ A z :=
  (hA.differentiableOn one_ne_zero).differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds hz)

theorem wirtinger_pull {A : ℂ → ℂ} (hA : ContDiffOn ℝ 1 A upperHalfPlaneSet) (g : SL(2, ℤ))
    {z : ℂ} (hz : 0 < z.im) :
    wirtinger (pull g A) z = (Complex.normSq ((den g z ^ 2)⁻¹) : ℂ) * wirtinger A (mob g z) := by
  have hm := hasDerivAt_mob g hz
  have hAd : DifferentiableAt ℝ A (mob g z) := differentiableAt_of_contDiffOn hA (im_mob_pos g hz)
  obtain ⟨h', hh⟩ : ∃ h', HasDerivAt (fun w ↦ (den g w ^ 2)⁻¹) h' z :=
    ⟨_, ((hasDerivAt_den g z).pow 2).inv (pow_ne_zero 2 (den_ne_zero g hz))⟩
  have hc : (fun w ↦ ((starRingEnd ℂ (den g w)) ^ 2)⁻¹) =
      fun w ↦ starRingEnd ℂ ((den g w ^ 2)⁻¹) := by
    funext w
    simp only [map_inv₀, map_pow]
  have e1 : wirtinger (fun w ↦ A (mob g w)) z = (den g z ^ 2)⁻¹ * wirtinger A (mob g z) :=
    wirtinger_comp_hasDerivAt hAd hm
  have e2 : wirtinger (fun w ↦ ((starRingEnd ℂ (den g w)) ^ 2)⁻¹) z = 0 := by
    rw [hc]
    exact wirtinger_conj_comp hh
  have hF : DifferentiableAt ℝ (fun w ↦ A (mob g w)) z :=
    hAd.comp z (hm.differentiableAt.restrictScalars ℝ)
  have hG : DifferentiableAt ℝ (fun w ↦ ((starRingEnd ℂ (den g w)) ^ 2)⁻¹) z := by
    rw [hc]
    exact Complex.conjCLE.differentiableAt.comp z (hh.differentiableAt.restrictScalars ℝ)
  rw [show pull g A = fun w ↦ (fun w ↦ A (mob g w)) w *
      (fun w ↦ ((starRingEnd ℂ (den g w)) ^ 2)⁻¹) w from rfl,
    wirtinger_mul hF hG, e1, e2, Complex.normSq_eq_conj_mul_self, map_inv₀, map_pow]
  ring

/-! ### The complex Jacobian and the change of variables (T203) -/

theorem det_smul_one (w : ℂ) : (w • (1 : ℂ →L[ℝ] ℂ)).det = Complex.normSq w := by
  rw [← Algebra.norm_complex_apply, Algebra.norm_apply]
  congr 1

theorem im_pos_of_mem_tile {H : ℝ} {z : ℂ} (hz : z ∈ tile H) : 0 < z.im := by
  obtain ⟨h0, -, hre, hn⟩ := hz
  have := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_nonneg h0] at this
  linarith

theorem isCompact_tile (H : ℝ) : IsCompact (tile H) := by
  rw [tile_eq_coe_image]
  exact (ModularGroup.isCompact_truncatedFundamentalDomain H).image UpperHalfPlane.continuous_coe

theorem measurableSet_tile (H : ℝ) : MeasurableSet (tile H) :=
  (isCompact_tile H).isClosed.measurableSet

theorem integral_mob_tile {A : ℂ → ℂ} (hA : ContDiffOn ℝ 1 A upperHalfPlaneSet) (g : SL(2, ℤ))
    (H : ℝ) : ∫ z in mob g '' tile H, wirtinger A z = ∫ z in tile H, wirtinger (pull g A) z := by
  have hf' : ∀ z ∈ tile H,
      HasFDerivWithinAt (mob g) ((den g z ^ 2)⁻¹ • (1 : ℂ →L[ℝ] ℂ)) (tile H) z := fun z hz ↦
    (hasDerivAt_mob g (im_pos_of_mem_tile hz)).complexToReal_fderiv.hasFDerivWithinAt
  have hinj : InjOn (mob g) (tile H) := (mob_injOn g).mono fun z hz ↦ im_pos_of_mem_tile hz
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume (measurableSet_tile H) hf' hinj]
  refine setIntegral_congr_fun (measurableSet_tile H) fun z hz ↦ ?_
  rw [wirtinger_pull hA g (im_pos_of_mem_tile hz), det_smul_one,
    abs_of_nonneg (Complex.normSq_nonneg _), Complex.real_smul]

/-! ### Fibrewise fundamental theorem of calculus (T204) -/

/-- The closed region between the graphs of `φ` and `ψ` over `s`, as a subset of `ℝ × ℝ`. -/
def closedRegion (φ ψ : ℝ → ℝ) (s : Set ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ s ∧ p.2 ∈ Icc (φ p.1) (ψ p.1)}

theorem integral_closedRegion {G g : ℝ × ℝ → ℂ} {φ ψ : ℝ → ℝ} {s : Set ℝ}
    (hφ : Measurable φ) (hψ : Measurable ψ) (hs : MeasurableSet s) (hle : ∀ x ∈ s, φ x ≤ ψ x)
    (hint : IntegrableOn g (closedRegion φ ψ s))
    (hderiv : ∀ x ∈ s, ∀ y ∈ Icc (φ x) (ψ x), HasDerivAt (fun t ↦ G (x, t)) (g (x, y)) y) :
    ∫ p in closedRegion φ ψ s, g p = ∫ x in s, (G (x, ψ x) - G (x, φ x)) := by
  have hR : MeasurableSet (closedRegion φ ψ s) := measurableSet_region_between_cc hφ hψ hs
  have hind : Integrable ((closedRegion φ ψ s).indicator g) (volume.prod volume) :=
    (integrable_indicator_iff hR).2 hint
  rw [← MeasureTheory.integral_indicator hR, Measure.volume_eq_prod, integral_prod _ hind,
    ← MeasureTheory.integral_indicator hs]
  refine integral_congr_ae ?_
  filter_upwards [hind.prod_right_ae] with x hx
  by_cases hxs : x ∈ s
  · have hslice : (fun y ↦ (closedRegion φ ψ s).indicator g (x, y)) =
        (Icc (φ x) (ψ x)).indicator (fun y ↦ g (x, y)) := by
      funext y
      simp [closedRegion, Set.indicator, hxs]
    have hxy := hle x hxs
    rw [hslice] at hx
    rw [hslice, Set.indicator_of_mem hxs, MeasureTheory.integral_indicator measurableSet_Icc,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hxy]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y hy ↦ hderiv x hxs y (by rwa [uIcc_of_le hxy] at hy)) ?_
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hxy, ← integrableOn_Icc_iff_integrableOn_Ioc]
    exact (integrable_indicator_iff measurableSet_Icc).1 hx
  · have hslice : (fun y ↦ (closedRegion φ ψ s).indicator g (x, y)) = fun _ ↦ 0 := by
      funext y
      simp [closedRegion, Set.indicator, hxs]
    simp [hslice, hxs]

/-- The closed region `{x + y i | x ∈ s, φ x ≤ y ≤ ψ x}` of `ℂ`. -/
def vRegion (φ ψ : ℝ → ℝ) (s : Set ℝ) : Set ℂ :=
  {z | z.re ∈ s ∧ z.im ∈ Icc (φ z.re) (ψ z.re)}

/-- The closed region `{x + y i | y ∈ s, φ y ≤ x ≤ ψ y}` of `ℂ`. -/
def hRegion (φ ψ : ℝ → ℝ) (s : Set ℝ) : Set ℂ :=
  {z | z.im ∈ s ∧ z.re ∈ Icc (φ z.im) (ψ z.im)}

theorem integral_vRegion {B g : ℂ → ℂ} {φ ψ : ℝ → ℝ} {s : Set ℝ} (hφ : Measurable φ)
    (hψ : Measurable ψ) (hs : MeasurableSet s) (hle : ∀ x ∈ s, φ x ≤ ψ x)
    (hint : IntegrableOn g (vRegion φ ψ s))
    (hderiv : ∀ x ∈ s, ∀ y ∈ Icc (φ x) (ψ x),
      HasDerivAt (fun t : ℝ ↦ B (x + t * Complex.I)) (g (x + y * Complex.I)) y) :
    ∫ z in vRegion φ ψ s, g z =
      ∫ x in s, (B (x + ψ x * Complex.I) - B (x + φ x * Complex.I)) := by
  have h₁ := Complex.volume_preserving_equiv_real_prod.symm
  have h₂ := Complex.measurableEquivRealProd.symm.measurableEmbedding
  have hpre : Complex.measurableEquivRealProd.symm ⁻¹' vRegion φ ψ s = closedRegion φ ψ s := by
    ext p
    simp [closedRegion, vRegion]
  rw [← h₁.setIntegral_preimage_emb h₂ g (vRegion φ ψ s), hpre]
  refine integral_closedRegion (G := fun p ↦ B (p.1 + p.2 * Complex.I)) hφ hψ hs hle ?_ ?_
  · rw [← hpre]
    exact (h₁.integrableOn_comp_preimage h₂).2 hint
  · intro x hx y hy
    simpa [Complex.mk_eq_add_mul_I] using hderiv x hx y hy

theorem integral_hRegion {B g : ℂ → ℂ} {φ ψ : ℝ → ℝ} {s : Set ℝ} (hφ : Measurable φ)
    (hψ : Measurable ψ) (hs : MeasurableSet s) (hle : ∀ y ∈ s, φ y ≤ ψ y)
    (hint : IntegrableOn g (hRegion φ ψ s))
    (hderiv : ∀ y ∈ s, ∀ x ∈ Icc (φ y) (ψ y),
      HasDerivAt (fun t : ℝ ↦ B (t + y * Complex.I)) (g (x + y * Complex.I)) x) :
    ∫ z in hRegion φ ψ s, g z =
      ∫ y in s, (B (ψ y + y * Complex.I) - B (φ y + y * Complex.I)) := by
  set e : ℂ ≃ᵐ ℝ × ℝ := Complex.measurableEquivRealProd.trans MeasurableEquiv.prodComm with he
  have h₁ : MeasurePreserving e.symm volume volume :=
    (Measure.measurePreserving_swap.comp Complex.volume_preserving_equiv_real_prod).symm e
  have h₂ := e.symm.measurableEmbedding
  have hswap : ∀ p : ℝ × ℝ, MeasurableEquiv.prodComm.symm p = p.swap := fun _ ↦ rfl
  have hpre : e.symm ⁻¹' hRegion φ ψ s = closedRegion φ ψ s := by
    ext p
    simp [closedRegion, hRegion, he, hswap]
  rw [← h₁.setIntegral_preimage_emb h₂ g (hRegion φ ψ s), hpre]
  refine integral_closedRegion (G := fun p ↦ B (p.2 + p.1 * Complex.I)) hφ hψ hs hle ?_ ?_
  · rw [← hpre]
    exact (h₁.integrableOn_comp_preimage h₂).2 hint
  · intro y hy x hx
    simpa [he, hswap, Complex.mk_eq_add_mul_I] using hderiv y hy x hx

/-! ### The rectangle, the lens and the tile (T205) -/

/-- The rectangle `{|x| ≤ 1/2, √3/2 ≤ y ≤ H}`. -/
def rect (H : ℝ) : Set ℂ := {z | |z.re| ≤ 1 / 2 ∧ Real.sqrt 3 / 2 ≤ z.im ∧ z.im ≤ H}

/-- The lens `{√3/2 ≤ y, ‖z‖ ≤ 1}` cut off the rectangle by the unit circle. -/
def lens : Set ℂ := {z | Real.sqrt 3 / 2 ≤ z.im ∧ ‖z‖ ≤ 1}

theorem norm_le_one_iff (z : ℂ) : ‖z‖ ≤ 1 ↔ z.re ^ 2 + z.im ^ 2 ≤ 1 := by
  rw [← sq_le_one_iff₀ (norm_nonneg z), Complex.sq_norm, Complex.normSq_apply]
  simp only [sq]

theorem one_le_norm_iff (z : ℂ) : 1 ≤ ‖z‖ ↔ 1 ≤ z.re ^ 2 + z.im ^ 2 := by
  rw [← one_le_sq_iff₀ (norm_nonneg z), Complex.sq_norm, Complex.normSq_apply]
  simp only [sq]

theorem sqrt3_half_pos : 0 < Real.sqrt 3 / 2 := by positivity

theorem sqrt3_half_le_iff {y : ℝ} (hy : 0 ≤ y) : Real.sqrt 3 / 2 ≤ y ↔ 3 / 4 ≤ y ^ 2 := by
  rw [div_le_iff₀ two_pos, Real.sqrt_le_left (by linarith)]
  constructor <;> intro h <;> nlinarith

theorem arcHeight_nonneg (x : ℝ) : 0 ≤ arcHeight x := Real.sqrt_nonneg _

theorem rect_eq_vRegion (H : ℝ) :
    rect H = vRegion (fun _ ↦ Real.sqrt 3 / 2) (fun _ ↦ H) (Icc (-1 / 2) (1 / 2)) := by
  ext z
  simp only [rect, vRegion, Set.mem_ofPred_eq, Set.mem_Icc, abs_le, neg_div]

theorem rect_eq_hRegion (H : ℝ) :
    rect H = hRegion (fun _ ↦ -1 / 2) (fun _ ↦ 1 / 2) (Icc (Real.sqrt 3 / 2) H) := by
  ext z
  simp only [rect, hRegion, Set.mem_ofPred_eq, Set.mem_Icc, abs_le, neg_div]
  tauto

theorem lens_eq_vRegion :
    lens = vRegion (fun _ ↦ Real.sqrt 3 / 2) arcHeight (Icc (-1 / 2) (1 / 2)) := by
  ext z
  simp only [lens, vRegion, Set.mem_ofPred_eq, Set.mem_Icc, norm_le_one_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have him : 0 ≤ z.im := by linarith [sqrt3_half_pos]
    have him2 := (sqrt3_half_le_iff him).1 h1
    refine ⟨⟨by nlinarith, by nlinarith⟩, h1, ?_⟩
    rw [arcHeight, Real.le_sqrt him (by nlinarith)]
    linarith
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    have him : 0 ≤ z.im := by linarith [sqrt3_half_pos]
    rw [arcHeight, Real.le_sqrt him (by nlinarith)] at h4
    exact ⟨h3, by linarith⟩

theorem lens_eq_hRegion :
    lens = hRegion (fun y ↦ -arcHeight y) arcHeight (Icc (Real.sqrt 3 / 2) 1) := by
  ext z
  simp only [lens, hRegion, Set.mem_ofPred_eq, Set.mem_Icc, norm_le_one_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have him : 0 ≤ z.im := by linarith [sqrt3_half_pos]
    have habs := Real.abs_le_sqrt (x := z.re) (y := 1 - z.im ^ 2) (by linarith)
    rw [abs_le] at habs
    exact ⟨⟨h1, by nlinarith⟩, habs.1, habs.2⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    have habs : |z.re| ≤ arcHeight z.im := abs_le.2 ⟨h3, h4⟩
    have him : 0 ≤ z.im := by linarith [sqrt3_half_pos]
    rw [arcHeight, Real.le_sqrt (abs_nonneg _) (by nlinarith), sq_abs] at habs
    exact ⟨h1, by linarith⟩

theorem tile_union_lens {H : ℝ} (hH : 1 ≤ H) : tile H ∪ lens = rect H := by
  ext z
  simp only [tile, lens, rect, Set.mem_union, Set.mem_ofPred_eq, one_le_norm_iff, norm_le_one_iff]
  constructor
  · rintro (⟨h0, hH', hre, hn⟩ | ⟨h1, h2⟩)
    · refine ⟨hre, ?_, hH'⟩
      rw [abs_le] at hre
      exact (sqrt3_half_le_iff h0).2 (by nlinarith)
    · have him : 0 ≤ z.im := by linarith [sqrt3_half_pos]
      have him2 := (sqrt3_half_le_iff him).1 h1
      refine ⟨abs_le.2 ⟨by nlinarith, by nlinarith⟩, h1, by nlinarith⟩
  · rintro ⟨hre, h1, h2⟩
    have him : 0 ≤ z.im := by linarith [sqrt3_half_pos]
    by_cases hn : 1 ≤ z.re ^ 2 + z.im ^ 2
    · exact Or.inl ⟨him, h2, hre, hn⟩
    · exact Or.inr ⟨h1, by linarith⟩

theorem tile_inter_lens_subset (H : ℝ) : tile H ∩ lens ⊆ Metric.sphere (0 : ℂ) 1 := by
  rintro z ⟨⟨-, -, -, hn⟩, -, hl⟩
  rw [mem_sphere_zero_iff_norm]
  exact le_antisymm hl hn

theorem isCompact_rect (H : ℝ) : IsCompact (rect H) := by
  have : rect H = Complex.equivRealProdCLM.toHomeomorph ⁻¹'
      (Icc (-1 / 2) (1 / 2) ×ˢ Icc (Real.sqrt 3 / 2) H) := by
    ext z
    simp only [rect, Set.mem_ofPred_eq, Set.mem_preimage, ContinuousLinearEquiv.coe_toHomeomorph,
      Complex.equivRealProdCLM_apply, Set.mem_prod, Set.mem_Icc, abs_le, neg_div]
  rw [this, Homeomorph.isCompact_preimage]
  exact isCompact_Icc.prod isCompact_Icc

theorem isCompact_lens : IsCompact lens := by
  have : lens = Metric.closedBall (0 : ℂ) 1 ∩ {z | Real.sqrt 3 / 2 ≤ z.im} := by
    ext z
    simp only [lens, Set.mem_ofPred_eq, Set.mem_inter_iff, mem_closedBall_zero_iff]
    tauto
  rw [this]
  exact (isCompact_closedBall (0 : ℂ) 1).inter_right
    (isClosed_le continuous_const Complex.continuous_im)

theorem measurableSet_rect (H : ℝ) : MeasurableSet (rect H) :=
  (isCompact_rect H).isClosed.measurableSet

theorem measurableSet_lens : MeasurableSet lens := isCompact_lens.isClosed.measurableSet

theorem rect_subset (H : ℝ) : rect H ⊆ upperHalfPlaneSet := fun _ hz ↦
  lt_of_lt_of_le sqrt3_half_pos hz.2.1

theorem lens_subset : lens ⊆ upperHalfPlaneSet := fun _ hz ↦ lt_of_lt_of_le sqrt3_half_pos hz.1

theorem integral_tile_eq_sub {H : ℝ} (hH : 1 ≤ H) {g : ℂ → ℂ} (hg : IntegrableOn g (rect H)) :
    ∫ z in tile H, g z = (∫ z in rect H, g z) - ∫ z in lens, g z := by
  have hsub1 : tile H ⊆ rect H := tile_union_lens hH ▸ subset_union_left
  have hsub2 : lens ⊆ rect H := tile_union_lens hH ▸ subset_union_right
  have hdisj : AEDisjoint volume (tile H) lens :=
    measure_mono_null (tile_inter_lens_subset H) (Measure.addHaar_sphere volume 0 1)
  rw [← tile_union_lens hH, setIntegral_union₀ hdisj measurableSet_lens.nullMeasurableSet
    (hg.mono_set hsub1) (hg.mono_set hsub2), add_sub_cancel_right]

/-! ### Green's theorem on the truncated standard tile (T206) -/

theorem continuousOn_fderiv_apply {B : ℂ → ℂ} (hB : ContDiffOn ℝ 1 B upperHalfPlaneSet) (v : ℂ) :
    ContinuousOn (fun z ↦ fderiv ℝ B z v) upperHalfPlaneSet :=
  (hB.continuousOn_fderiv_of_isOpen isOpen_upperHalfPlaneSet le_rfl).clm_apply continuousOn_const

theorem continuousOn_wirtinger {B : ℂ → ℂ} (hB : ContDiffOn ℝ 1 B upperHalfPlaneSet) :
    ContinuousOn (wirtinger B) upperHalfPlaneSet := by
  change ContinuousOn
    (fun z ↦ (1 / 2 : ℂ) * (fderiv ℝ B z 1 - Complex.I * fderiv ℝ B z Complex.I)) _
  exact continuousOn_const.mul ((continuousOn_fderiv_apply hB 1).sub
    (continuousOn_const.mul (continuousOn_fderiv_apply hB Complex.I)))

theorem im_add_mul_I (x y : ℝ) : ((x : ℂ) + y * Complex.I).im = y := by simp

theorem hasDerivAt_vertical {B : ℂ → ℂ} (x y : ℝ)
    (hB : DifferentiableAt ℝ B (x + y * Complex.I)) :
    HasDerivAt (fun t : ℝ ↦ B (x + t * Complex.I)) (fderiv ℝ B (x + y * Complex.I) Complex.I) y := by
  have h1 : HasDerivAt (fun t : ℝ ↦ (x : ℂ) + t * Complex.I) Complex.I y := by
    simpa using ((hasDerivAt_id y).ofReal_comp.mul_const Complex.I).const_add (x : ℂ)
  exact hB.hasFDerivAt.comp_hasDerivAt y h1

theorem hasDerivAt_horizontal {B : ℂ → ℂ} (x y : ℝ)
    (hB : DifferentiableAt ℝ B (x + y * Complex.I)) :
    HasDerivAt (fun t : ℝ ↦ B (t + y * Complex.I)) (fderiv ℝ B (x + y * Complex.I) 1) x := by
  have h1 : HasDerivAt (fun t : ℝ ↦ (t : ℂ) + y * Complex.I) 1 x := by
    simpa using (hasDerivAt_id x).ofReal_comp.add_const ((y : ℂ) * Complex.I)
  exact hB.hasFDerivAt.comp_hasDerivAt x h1

theorem sq_sqrt3_half : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem sqrt3_half_le_one : Real.sqrt 3 / 2 ≤ 1 :=
  (sqrt3_half_le_iff zero_le_one).2 (by norm_num)

@[fun_prop]
theorem continuous_arcHeight : Continuous arcHeight :=
  Real.continuous_sqrt.comp (by fun_prop)

theorem measurable_arcHeight : Measurable arcHeight := continuous_arcHeight.measurable

theorem sq_arcHeight {x : ℝ} (hx : x ^ 2 ≤ 1) : arcHeight x ^ 2 = 1 - x ^ 2 :=
  Real.sq_sqrt (by linarith)

theorem arcHeight_pos {x : ℝ} (hx : x ^ 2 < 1) : 0 < arcHeight x :=
  Real.sqrt_pos.2 (by linarith)

theorem sqrt3_half_le_arcHeight {x : ℝ} (hx : x ^ 2 ≤ 1 / 4) : Real.sqrt 3 / 2 ≤ arcHeight x := by
  rw [arcHeight, Real.le_sqrt sqrt3_half_pos.le (by linarith), sq_sqrt3_half]
  linarith

theorem arcHeight_arcHeight {x : ℝ} (hx : x ^ 2 ≤ 1) : arcHeight (arcHeight x) = |x| := by
  rw [arcHeight, sq_arcHeight hx, sub_sub_cancel, Real.sqrt_sq_eq_abs]

theorem arcHeight_half : arcHeight (1 / 2) = Real.sqrt 3 / 2 := by
  rw [arcHeight, Real.sqrt_eq_iff_eq_sq (by norm_num) sqrt3_half_pos.le, sq_sqrt3_half]
  norm_num

theorem arcHeight_neg (x : ℝ) : arcHeight (-x) = arcHeight x := by
  simp [arcHeight]

theorem arcHeight_zero : arcHeight 0 = 1 := by
  simp [arcHeight]

theorem hasDerivAt_arcHeight {x : ℝ} (hx : x ^ 2 < 1) :
    HasDerivAt arcHeight (-x / arcHeight x) x := by
  have h : HasDerivAt (fun y : ℝ ↦ 1 - y ^ 2) (-(2 * x)) x := by
    simpa using (hasDerivAt_pow 2 x).const_sub 1
  have hne : (1 - x ^ 2) ≠ 0 := by linarith
  refine (h.sqrt hne).congr_deriv ?_
  have hpos : Real.sqrt (1 - x ^ 2) ≠ 0 := (arcHeight_pos hx).ne'
  rw [arcHeight]
  field_simp

theorem intervalIntegrable_comp_path {B : ℂ → ℂ} (hB : ContDiffOn ℝ 1 B upperHalfPlaneSet)
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : ContinuousOn γ (uIcc a b)) (him : ∀ t ∈ uIcc a b, 0 < (γ t).im) :
    IntervalIntegrable (fun t ↦ B (γ t)) volume a b :=
  (hB.continuousOn.comp hγ him).intervalIntegrable

theorem integral_rect_partialX {H : ℝ} (hH : Real.sqrt 3 / 2 ≤ H) {B : ℂ → ℂ}
    (hB : ContDiffOn ℝ 1 B upperHalfPlaneSet) :
    ∫ z in rect H, fderiv ℝ B z 1 = ∫ y in (Real.sqrt 3 / 2)..H,
      (B ((1 / 2 : ℝ) + y * Complex.I) - B ((-1 / 2 : ℝ) + y * Complex.I)) := by
  have hint : IntegrableOn (fun z ↦ fderiv ℝ B z 1) (rect H) :=
    ((continuousOn_fderiv_apply hB 1).mono (rect_subset H)).integrableOn_compact (isCompact_rect H)
  rw [rect_eq_hRegion] at hint
  rw [intervalIntegral.integral_of_le hH, ← integral_Icc_eq_integral_Ioc, rect_eq_hRegion]
  refine integral_hRegion measurable_const measurable_const measurableSet_Icc
    (fun _ _ ↦ by norm_num) hint fun y hy x hx ↦ ?_
  refine hasDerivAt_horizontal x y (differentiableAt_of_contDiffOn hB ?_)
  rw [im_add_mul_I]
  exact lt_of_lt_of_le sqrt3_half_pos hy.1

theorem integral_rect_partialY {H : ℝ} (hH : Real.sqrt 3 / 2 ≤ H) {B : ℂ → ℂ}
    (hB : ContDiffOn ℝ 1 B upperHalfPlaneSet) :
    ∫ z in rect H, fderiv ℝ B z Complex.I = ∫ x in (-1 / 2 : ℝ)..(1 / 2),
      (B (x + H * Complex.I) - B (x + (Real.sqrt 3 / 2 : ℝ) * Complex.I)) := by
  have hint : IntegrableOn (fun z ↦ fderiv ℝ B z Complex.I) (rect H) :=
    ((continuousOn_fderiv_apply hB Complex.I).mono (rect_subset H)).integrableOn_compact
      (isCompact_rect H)
  rw [rect_eq_vRegion] at hint
  rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc,
    rect_eq_vRegion]
  refine integral_vRegion measurable_const measurable_const measurableSet_Icc (fun _ _ ↦ hH) hint
    fun x hx y hy ↦ ?_
  refine hasDerivAt_vertical x y (differentiableAt_of_contDiffOn hB ?_)
  rw [im_add_mul_I]
  exact lt_of_lt_of_le sqrt3_half_pos hy.1

theorem integral_lens_partialX {B : ℂ → ℂ} (hB : ContDiffOn ℝ 1 B upperHalfPlaneSet) :
    ∫ z in lens, fderiv ℝ B z 1 = ∫ y in (Real.sqrt 3 / 2)..1,
      (B (arcHeight y + y * Complex.I) - B ((-arcHeight y : ℝ) + y * Complex.I)) := by
  have hint : IntegrableOn (fun z ↦ fderiv ℝ B z 1) lens :=
    ((continuousOn_fderiv_apply hB 1).mono lens_subset).integrableOn_compact isCompact_lens
  rw [lens_eq_hRegion] at hint
  rw [intervalIntegral.integral_of_le sqrt3_half_le_one, ← integral_Icc_eq_integral_Ioc,
    lens_eq_hRegion]
  refine integral_hRegion measurable_arcHeight.neg measurable_arcHeight measurableSet_Icc
    (fun y _ ↦ by linarith [arcHeight_nonneg y]) hint fun y hy x hx ↦ ?_
  refine hasDerivAt_horizontal x y (differentiableAt_of_contDiffOn hB ?_)
  rw [im_add_mul_I]
  exact lt_of_lt_of_le sqrt3_half_pos hy.1

theorem integral_lens_partialY {B : ℂ → ℂ} (hB : ContDiffOn ℝ 1 B upperHalfPlaneSet) :
    ∫ z in lens, fderiv ℝ B z Complex.I = ∫ x in (-1 / 2 : ℝ)..(1 / 2),
      (B (x + arcHeight x * Complex.I) - B (x + (Real.sqrt 3 / 2 : ℝ) * Complex.I)) := by
  have hint : IntegrableOn (fun z ↦ fderiv ℝ B z Complex.I) lens :=
    ((continuousOn_fderiv_apply hB Complex.I).mono lens_subset).integrableOn_compact
      isCompact_lens
  rw [lens_eq_vRegion] at hint
  rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc,
    lens_eq_vRegion]
  refine integral_vRegion measurable_const measurable_arcHeight measurableSet_Icc
    (fun x hx ↦ sqrt3_half_le_arcHeight (by nlinarith [hx.1, hx.2])) hint fun x hx y hy ↦ ?_
  refine hasDerivAt_vertical x y (differentiableAt_of_contDiffOn hB ?_)
  rw [im_add_mul_I]
  exact lt_of_lt_of_le sqrt3_half_pos hy.1

theorem continuousOn_arcPath {B : ℂ → ℂ} (hB : ContDiffOn ℝ 1 B upperHalfPlaneSet) :
    ContinuousOn (fun x : ℝ ↦ B (x + arcHeight x * Complex.I)) (Icc (-1 / 2) (1 / 2)) := by
  refine hB.continuousOn.comp (by fun_prop) fun x hx ↦ ?_
  change 0 < ((x : ℂ) + arcHeight x * Complex.I).im
  rw [im_add_mul_I]
  exact arcHeight_pos (by nlinarith [hx.1, hx.2])

theorem integral_arc_y_eq {B : ℂ → ℂ} (hB : ContDiffOn ℝ 1 B upperHalfPlaneSet) :
    ∫ y in (Real.sqrt 3 / 2)..1,
        (B (arcHeight y + y * Complex.I) - B ((-arcHeight y : ℝ) + y * Complex.I)) =
      ∫ x in (-1 / 2 : ℝ)..(1 / 2), (x / arcHeight x : ℝ) • B (x + arcHeight x * Complex.I) := by
  have hBc : ContinuousOn B upperHalfPlaneSet := hB.continuousOn
  have hG₁ : ContinuousOn (fun y : ℝ ↦ B (arcHeight y + y * Complex.I)) (Ioi 0) := by
    refine hBc.comp (by fun_prop) fun y hy ↦ ?_
    change 0 < ((arcHeight y : ℂ) + y * Complex.I).im
    rw [im_add_mul_I]
    exact hy
  have hG₂ : ContinuousOn (fun y : ℝ ↦ B ((-arcHeight y : ℝ) + y * Complex.I)) (Ioi 0) := by
    refine hBc.comp (by fun_prop) fun y hy ↦ ?_
    change 0 < (((-arcHeight y : ℝ) : ℂ) + y * Complex.I).im
    rw [im_add_mul_I]
    exact hy
  have hIcc : Icc (Real.sqrt 3 / 2) 1 ⊆ Ioi 0 := fun y hy ↦ lt_of_lt_of_le sqrt3_half_pos hy.1
  have hderiv : ∀ x ∈ Icc (-1 / 2 : ℝ) (1 / 2), HasDerivAt arcHeight (-x / arcHeight x) x :=
    fun x hx ↦ hasDerivAt_arcHeight (by nlinarith [hx.1, hx.2])
  have hderiv_cont : ContinuousOn (fun x : ℝ ↦ -x / arcHeight x) (Icc (-1 / 2) (1 / 2)) :=
    (continuousOn_id.neg).div continuous_arcHeight.continuousOn fun x hx ↦
      (arcHeight_pos (by nlinarith [hx.1, hx.2])).ne'
  have himg : ∀ x ∈ Icc (-1 / 2 : ℝ) (1 / 2), arcHeight x ∈ Ioi 0 := fun x hx ↦
    arcHeight_pos (by nlinarith [hx.1, hx.2])
  -- the right half of the arc, `x ∈ [0, 1/2]`
  have hA : ∫ y in (Real.sqrt 3 / 2)..1, B (arcHeight y + y * Complex.I) =
      ∫ x in (0 : ℝ)..(1 / 2), (x / arcHeight x : ℝ) • B (x + arcHeight x * Complex.I) := by
    have hsub : Icc (0 : ℝ) (1 / 2) ⊆ Icc (-1 / 2) (1 / 2) := Icc_subset_Icc (by norm_num) le_rfl
    have := intervalIntegral.integral_deriv_smul_comp' (a := 1 / 2) (b := 0)
      (f := arcHeight) (f' := fun x ↦ -x / arcHeight x)
      (g := fun y : ℝ ↦ B (arcHeight y + y * Complex.I))
      (fun x hx ↦ hderiv x (hsub (by rwa [uIcc_of_ge (by norm_num)] at hx)))
      (by rw [uIcc_of_ge (by norm_num)]; exact hderiv_cont.mono hsub)
      (hG₁.mono (by rw [uIcc_of_ge (by norm_num)]; rintro _ ⟨x, hx, rfl⟩; exact himg x (hsub hx)))
    rw [arcHeight_half, arcHeight_zero] at this
    rw [← this, intervalIntegral.integral_symm, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun x hx ↦ ?_
    rw [uIcc_of_le (by norm_num)] at hx
    simp only [Function.comp, arcHeight_arcHeight (by nlinarith [hx.1, hx.2] : x ^ 2 ≤ 1),
      abs_of_nonneg hx.1, neg_div, _root_.neg_smul, neg_neg]
  -- the left half of the arc, `x ∈ [-1/2, 0]`
  have hB' : ∫ y in (Real.sqrt 3 / 2)..1, B ((-arcHeight y : ℝ) + y * Complex.I) =
      -∫ x in (-1 / 2 : ℝ)..0, (x / arcHeight x : ℝ) • B (x + arcHeight x * Complex.I) := by
    have hsub : Icc (-1 / 2 : ℝ) 0 ⊆ Icc (-1 / 2) (1 / 2) := Icc_subset_Icc le_rfl (by norm_num)
    have := intervalIntegral.integral_deriv_smul_comp' (a := -1 / 2) (b := 0)
      (f := arcHeight) (f' := fun x ↦ -x / arcHeight x)
      (g := fun y : ℝ ↦ B ((-arcHeight y : ℝ) + y * Complex.I))
      (fun x hx ↦ hderiv x (hsub (by rwa [uIcc_of_le (by norm_num)] at hx)))
      (by rw [uIcc_of_le (by norm_num)]; exact hderiv_cont.mono hsub)
      (hG₂.mono (by rw [uIcc_of_le (by norm_num)]; rintro _ ⟨x, hx, rfl⟩; exact himg x (hsub hx)))
    rw [show arcHeight (-1 / 2) = Real.sqrt 3 / 2 by rw [neg_div, arcHeight_neg, arcHeight_half],
      arcHeight_zero] at this
    rw [← this, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun x hx ↦ ?_
    rw [uIcc_of_le (by norm_num)] at hx
    simp only [Function.comp, arcHeight_arcHeight (by nlinarith [hx.1, hx.2] : x ^ 2 ≤ 1),
      abs_of_nonpos hx.2, neg_neg, neg_div, _root_.neg_smul]
  have hdiv : ContinuousOn (fun x : ℝ ↦ x / arcHeight x) (Icc (-1 / 2) (1 / 2)) :=
    continuousOn_id.div continuous_arcHeight.continuousOn fun x hx ↦
      (arcHeight_pos (by nlinarith [hx.1, hx.2])).ne'
  have hsm : ∀ a b, a ∈ Icc (-1 / 2 : ℝ) (1 / 2) → b ∈ Icc (-1 / 2 : ℝ) (1 / 2) →
      IntervalIntegrable (fun x : ℝ ↦ (x / arcHeight x : ℝ) • B (x + arcHeight x * Complex.I))
        volume a b := fun a b ha hb ↦
    ((hdiv.mono (uIcc_subset_Icc ha hb)).smul
      ((continuousOn_arcPath hB).mono (uIcc_subset_Icc ha hb))).intervalIntegrable
  rw [intervalIntegral.integral_sub
    (hG₁.mono (by rw [uIcc_of_le sqrt3_half_le_one]; exact hIcc)).intervalIntegrable
    (hG₂.mono (by rw [uIcc_of_le sqrt3_half_le_one]; exact hIcc)).intervalIntegrable,
    hA, hB', sub_neg_eq_add, add_comm,
    intervalIntegral.integral_add_adjacent_intervals (hsm _ _ (by norm_num) (by norm_num))
      (hsm _ _ (by norm_num) (by norm_num))]

/-- The left side `∫ B dy` over `{-1/2 + i y | √3/2 ≤ y ≤ H}`. -/
def sideL (H : ℝ) (B : ℂ → ℂ) : ℂ :=
  ∫ y in (Real.sqrt 3 / 2)..H, B ((-1 / 2 : ℝ) + y * Complex.I)

/-- The right side `∫ B dy` over `{1/2 + i y | √3/2 ≤ y ≤ H}`. -/
def sideR (H : ℝ) (B : ℂ → ℂ) : ℂ :=
  ∫ y in (Real.sqrt 3 / 2)..H, B ((1 / 2 : ℝ) + y * Complex.I)

/-- The arc term `∫ B dz̄` over the unit arc from `ρ + 1` to `ρ`, in the `x`-parametrisation. -/
def arc (B : ℂ → ℂ) : ℂ :=
  ∫ x in (-1 / 2 : ℝ)..(1 / 2),
    B (x + arcHeight x * Complex.I) * (1 + (x / arcHeight x : ℝ) * Complex.I)

/-- The cap term `∫ B dx` over `{x + i H | |x| ≤ 1/2}`. -/
def cap (H : ℝ) (B : ℂ → ℂ) : ℂ := ∫ x in (-1 / 2 : ℝ)..(1 / 2), B (x + H * Complex.I)

theorem tile_subset (H : ℝ) : tile H ⊆ upperHalfPlaneSet := fun _ hz ↦ im_pos_of_mem_tile hz

theorem tile_stokes {H : ℝ} (hH : 1 ≤ H) {B : ℂ → ℂ} (hB : ContDiffOn ℝ 1 B upperHalfPlaneSet) :
    ∫ z in tile H, wirtinger B z =
      (1 / 2 : ℂ) * (sideR H B - sideL H B) + (Complex.I / 2) * arc B -
        (Complex.I / 2) * cap H B := by
  have hH' : Real.sqrt 3 / 2 ≤ H := sqrt3_half_le_one.trans hH
  have h1 : IntegrableOn (fun z ↦ fderiv ℝ B z 1) (rect H) :=
    ((continuousOn_fderiv_apply hB 1).mono (rect_subset H)).integrableOn_compact (isCompact_rect H)
  have hI : IntegrableOn (fun z ↦ fderiv ℝ B z Complex.I) (rect H) :=
    ((continuousOn_fderiv_apply hB Complex.I).mono (rect_subset H)).integrableOn_compact
      (isCompact_rect H)
  have hsub : tile H ⊆ rect H := tile_union_lens hH ▸ subset_union_left
  have hvert : ∀ c : ℝ, IntervalIntegrable (fun y : ℝ ↦ B (c + y * Complex.I)) volume
      (Real.sqrt 3 / 2) H := fun c ↦
    intervalIntegrable_comp_path hB (by fun_prop) fun y hy ↦ by
      rw [uIcc_of_le hH'] at hy
      rw [im_add_mul_I]
      exact lt_of_lt_of_le sqrt3_half_pos hy.1
  have hhor : ∀ c : ℝ, 0 < c → IntervalIntegrable (fun x : ℝ ↦ B (x + c * Complex.I)) volume
      (-1 / 2) (1 / 2) := fun c hc ↦
    intervalIntegrable_comp_path hB (by fun_prop) fun x _ ↦ by
      rw [im_add_mul_I]
      exact hc
  have harcI : IntervalIntegrable (fun x : ℝ ↦ B (x + arcHeight x * Complex.I)) volume
      (-1 / 2) (1 / 2) :=
    ((continuousOn_arcPath hB).mono (by rw [uIcc_of_le (by norm_num)])).intervalIntegrable
  have hsmI : IntervalIntegrable
      (fun x : ℝ ↦ (x / arcHeight x : ℝ) • B (x + arcHeight x * Complex.I)) volume
      (-1 / 2) (1 / 2) := by
    have hdiv : ContinuousOn (fun x : ℝ ↦ x / arcHeight x) (Icc (-1 / 2) (1 / 2)) :=
      continuousOn_id.div continuous_arcHeight.continuousOn fun x hx ↦
        (arcHeight_pos (by nlinarith [hx.1, hx.2])).ne'
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (by norm_num)]
    exact hdiv.smul (continuousOn_arcPath hB)
  set A₀ := ∫ x in (-1 / 2 : ℝ)..(1 / 2), B (x + arcHeight x * Complex.I) with hA₀
  set A₁ := ∫ x in (-1 / 2 : ℝ)..(1 / 2),
    (x / arcHeight x : ℝ) • B (x + arcHeight x * Complex.I) with hA₁
  have hx : ∫ z in tile H, fderiv ℝ B z 1 = (sideR H B - sideL H B) - A₁ := by
    rw [integral_tile_eq_sub hH h1, integral_rect_partialX hH' hB, integral_lens_partialX hB,
      integral_arc_y_eq hB, sideR, sideL, intervalIntegral.integral_sub (hvert _) (hvert _)]
  have hy : ∫ z in tile H, fderiv ℝ B z Complex.I = cap H B - A₀ := by
    rw [integral_tile_eq_sub hH hI, integral_rect_partialY hH' hB, integral_lens_partialY hB, cap,
      intervalIntegral.integral_sub (hhor _ (by linarith)) (hhor _ sqrt3_half_pos),
      intervalIntegral.integral_sub harcI (hhor _ sqrt3_half_pos)]
    ring
  have harc : arc B = A₀ + Complex.I * A₁ := by
    rw [arc, hA₀, hA₁, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add harcI (hsmI.const_mul Complex.I)]
    refine intervalIntegral.integral_congr fun x _ ↦ ?_
    simp only [Complex.real_smul]
    ring
  have hw : ∫ z in tile H, wirtinger B z = (1 / 2 : ℂ) *
      ((∫ z in tile H, fderiv ℝ B z 1) - Complex.I * ∫ z in tile H, fderiv ℝ B z Complex.I) := by
    simp only [wirtinger]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_sub (h1.mono_set hsub)
      ((hI.mono_set hsub).const_mul _), MeasureTheory.integral_const_mul]
  rw [hw, hx, hy, harc]
  linear_combination (-(1 / 2 : ℂ) * A₁) * Complex.I_sq

/-! ### Edge pairing under `T` and `S` (T207) -/

theorem mob_T (z : ℂ) : mob ModularGroup.T z = z + 1 := by
  simp [mob, ModularGroup.coe_T]

theorem den_T (z : ℂ) : den ModularGroup.T z = 1 := by
  simp [den, ModularGroup.coe_T]

theorem mob_S (z : ℂ) : mob ModularGroup.S z = -z⁻¹ := by
  simp [mob, ModularGroup.coe_S, neg_div]

theorem den_S (z : ℂ) : den ModularGroup.S z = z := by
  simp [den, ModularGroup.coe_S]

theorem pull_T (B : ℂ → ℂ) (z : ℂ) : pull ModularGroup.T B z = B (z + 1) := by
  simp [pull, mob_T, den_T]

theorem pull_S (B : ℂ → ℂ) (z : ℂ) :
    pull ModularGroup.S B z = B (-z⁻¹) * ((starRingEnd ℂ z) ^ 2)⁻¹ := by
  simp only [pull, mob_S, den_S]

theorem sideR_eq_sideL_pull_T (H : ℝ) (B : ℂ → ℂ) :
    sideR H B = sideL H (pull ModularGroup.T B) := by
  refine intervalIntegral.integral_congr fun y _ ↦ ?_
  rw [pull_T]
  congr 1
  push_cast
  ring

theorem pull_S_arc (B : ℂ → ℂ) {x : ℝ} (hx : x ^ 2 ≤ 1) :
    pull ModularGroup.S B (x + arcHeight x * Complex.I) =
      B ((-x : ℝ) + arcHeight x * Complex.I) * ((x : ℂ) + arcHeight x * Complex.I) ^ 2 := by
  have hφ : (arcHeight x : ℂ) ^ 2 = 1 - (x : ℂ) ^ 2 := by exact_mod_cast sq_arcHeight hx
  have hw : ((x : ℂ) + arcHeight x * Complex.I) * ((x : ℂ) - arcHeight x * Complex.I) = 1 := by
    linear_combination hφ - (arcHeight x : ℂ) ^ 2 * Complex.I_sq
  have hinv : ((x : ℂ) + arcHeight x * Complex.I)⁻¹ = (x : ℂ) - arcHeight x * Complex.I :=
    inv_eq_of_mul_eq_one_right hw
  have hinv' : ((x : ℂ) - arcHeight x * Complex.I)⁻¹ = (x : ℂ) + arcHeight x * Complex.I :=
    inv_eq_of_mul_eq_one_right (by rw [mul_comm]; exact hw)
  have hconj : starRingEnd ℂ ((x : ℂ) + arcHeight x * Complex.I) =
      (x : ℂ) - arcHeight x * Complex.I := by
    simp [sub_eq_add_neg]
  rw [pull_S, hinv, hconj, ← inv_pow, hinv']
  congr 2
  push_cast
  ring

theorem arc_identity {x φ : ℝ} (hφ : φ ^ 2 = 1 - x ^ 2) (hφ0 : φ ≠ 0) :
    ((-x : ℝ) + φ * Complex.I) ^ 2 * (1 + ((-x) / φ : ℝ) * Complex.I) =
      -(1 + (x / φ : ℝ) * Complex.I) := by
  have hq : x / φ * φ = x := div_mul_cancel₀ x hφ0
  rw [neg_div]
  generalize x / φ = q at hq ⊢
  refine Complex.ext ?_ ?_
  · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.one_re,
      Complex.one_im, Complex.ofReal_neg, sq]
    linear_combination (-1 : ℝ) * hφ + (-2 * x) * hq
  · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.one_re,
      Complex.one_im, Complex.ofReal_neg, sq]
    linear_combination (-q) * hφ + 2 * φ * hq

theorem arc_pull_S (B : ℂ → ℂ) : arc (pull ModularGroup.S B) = -arc B := by
  rw [arc, arc, ← intervalIntegral.integral_neg]
  set G : ℝ → ℂ := fun u ↦ B (u + arcHeight u * Complex.I) *
    ((-u : ℝ) + arcHeight u * Complex.I) ^ 2 * (1 + ((-u) / arcHeight u : ℝ) * Complex.I) with hG
  have h1 : ∀ x ∈ uIcc (-1 / 2 : ℝ) (1 / 2),
      pull ModularGroup.S B (x + arcHeight x * Complex.I) *
        (1 + (x / arcHeight x : ℝ) * Complex.I) = G (-x) := by
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    rw [pull_S_arc B (by nlinarith [hx.1, hx.2])]
    simp only [hG, arcHeight_neg, neg_neg]
  rw [intervalIntegral.integral_congr h1, intervalIntegral.integral_comp_neg (f := G),
    show -(1 / 2 : ℝ) = -1 / 2 by norm_num, show -(-1 / 2 : ℝ) = 1 / 2 by norm_num]
  refine intervalIntegral.integral_congr fun x hx ↦ ?_
  rw [uIcc_of_le (by norm_num)] at hx
  have hx1 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
  simp only [hG]
  rw [mul_assoc, arc_identity (sq_arcHeight hx1) (arcHeight_pos (by nlinarith [hx.1, hx.2])).ne']
  ring

/-! ### The permutation of coset representatives (T208) -/

theorem sum_comp_mul_right {Γ : Subgroup SL(2, ℤ)} {R : Finset SL(2, ℤ)}
    (hR : Subgroup.IsComplement (Γ : Set SL(2, ℤ)) (R : Set SL(2, ℤ))) (h : SL(2, ℤ))
    {F : SL(2, ℤ) → ℂ} (hF : ∀ γ ∈ Γ, ∀ g, F (γ * g) = F g) :
    ∑ g ∈ R, F (g * h) = ∑ g ∈ R, F g := by
  have key : ∀ (k : SL(2, ℤ)) (g : SL(2, ℤ)), g ∈ R →
      ((hR.equiv (((hR.equiv (g * k)).2 : SL(2, ℤ)) * k⁻¹)).2 : SL(2, ℤ)) = g := by
    intro k g hg
    have e1 : ((hR.equiv (g * k)).2 : SL(2, ℤ)) * k⁻¹ = (((hR.equiv (g * k)).1 : SL(2, ℤ)))⁻¹ * g := by
      rw [hR.equiv_snd_eq_inv_mul]
      group
    rw [e1, hR.equiv_mul_left_of_mem (inv_mem (hR.equiv (g * k)).1.2)]
    exact congrArg Subtype.val (hR.equiv_snd_eq_self_of_mem_of_one_mem Γ.one_mem hg)
  refine Finset.sum_nbij' (fun g ↦ ((hR.equiv (g * h)).2 : SL(2, ℤ)))
    (fun g ↦ ((hR.equiv (g * h⁻¹)).2 : SL(2, ℤ))) (fun g _ ↦ (hR.equiv (g * h)).2.2)
    (fun g _ ↦ (hR.equiv (g * h⁻¹)).2.2) (fun g hg ↦ key h g hg) (fun g hg ↦ ?_) fun g _ ↦ ?_
  · simpa using key h⁻¹ g hg
  · conv_lhs => rw [← hR.equiv_fst_mul_equiv_snd (g * h)]
    exact hF _ (hR.equiv (g * h)).1.2 _

/-! ### Cap estimate and the limit `H → ∞` (T209) -/

theorem pull_apply_coe (g : SL(2, ℤ)) (A : ℂ → ℂ) (τ : ℍ) :
    pull g A τ = A ((g • τ : ℍ) : ℂ) * ((starRingEnd ℂ (denom g τ)) ^ 2)⁻¹ := by
  simp only [pull, mob_eq_coe_smul, den_eq_denom]

theorem tendsto_cap {A : ℂ → ℂ} (g : SL(2, ℤ))
    (hdecay : IsZeroAtImInfty
      fun τ : ℍ ↦ A ((g • τ : ℍ) : ℂ) * ((starRingEnd ℂ (denom g τ)) ^ 2)⁻¹) :
    Tendsto (fun H : ℝ ↦ cap H (pull g A)) atTop (𝓝 0) := by
  rw [UpperHalfPlane.isZeroAtImInfty_iff] at hdecay
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := hdecay (ε / 2) (by positivity)
  refine ⟨max M 1, fun H hH ↦ ?_⟩
  rw [dist_zero_right, cap]
  have hHpos : 0 < H := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hH)
  have hbound : ∀ x ∈ Set.uIoc (-1 / 2 : ℝ) (1 / 2), ‖pull g A (x + H * Complex.I)‖ ≤ ε / 2 := by
    intro x _
    have hτ : 0 < ((x : ℂ) + H * Complex.I).im := by rw [im_add_mul_I]; exact hHpos
    have := hM ⟨(x : ℂ) + H * Complex.I, hτ⟩ (by
      change M ≤ ((x : ℂ) + H * Complex.I).im
      rw [im_add_mul_I]
      exact le_trans (le_max_left _ _) hH)
    rw [← pull_apply_coe] at this
    exact this
  calc ‖∫ x in (-1 / 2 : ℝ)..(1 / 2), pull g A (x + H * Complex.I)‖
      ≤ ε / 2 * |1 / 2 - (-1 / 2 : ℝ)| := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ < ε := by norm_num; linarith

theorem continuousOn_mob (g : SL(2, ℤ)) (H : ℝ) : ContinuousOn (mob g) (tile H) := fun _ hz ↦
  (hasDerivAt_mob g (im_pos_of_mem_tile hz)).continuousAt.continuousWithinAt

theorem tendsto_integral_mob_tile {A : ℂ → ℂ} (g : SL(2, ℤ))
    (hint : IntegrableOn (wirtinger A) (mob g '' (UpperHalfPlane.coe '' 𝒟))) :
    Tendsto (fun H : ℝ ↦ ∫ z in mob g '' tile H, wirtinger A z) atTop
      (𝓝 (∫ z in mob g '' (UpperHalfPlane.coe '' 𝒟), wirtinger A z)) := by
  have hU : (⋃ H : ℝ, mob g '' tile H) = mob g '' (UpperHalfPlane.coe '' 𝒟) := by
    rw [← Set.image_iUnion]
    congr 1
    ext z
    simp only [Set.mem_iUnion, tile_eq_coe_image]
    constructor
    · rintro ⟨H, τ, hτ, rfl⟩
      exact ⟨τ, hτ.1, rfl⟩
    · rintro ⟨τ, hτ, rfl⟩
      exact ⟨τ.im, τ, ⟨hτ, le_rfl⟩, rfl⟩
  rw [← hU]
  refine tendsto_setIntegral_of_monotone (fun H ↦ ?_) (fun H₁ H₂ hle ↦ Set.image_mono ?_)
    (hU ▸ hint)
  · exact ((isCompact_tile H).image_of_continuousOn (continuousOn_mob g H)).isClosed.measurableSet
  · intro z hz
    exact ⟨hz.1, hz.2.1.trans hle, hz.2.2⟩

theorem contDiff_den (g : SL(2, ℤ)) : ContDiff ℝ 1 (den g) := by
  change ContDiff ℝ 1 (fun z : ℂ ↦ (g 1 0 : ℂ) * z + (g 1 1 : ℂ))
  fun_prop

theorem contDiffOn_mob (g : SL(2, ℤ)) : ContDiffOn ℝ 1 (mob g) upperHalfPlaneSet := by
  have : ContDiffOn ℂ 1 (mob g) upperHalfPlaneSet := by
    change ContDiffOn ℂ 1
      (fun z : ℂ ↦ ((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) / ((g 1 0 : ℂ) * z + (g 1 1 : ℂ))) _
    exact ContDiffOn.div (by fun_prop) (by fun_prop) fun z hz ↦ den_ne_zero g hz
  exact this.restrict_scalars ℝ

theorem contDiffOn_pull {A : ℂ → ℂ} (hA : ContDiffOn ℝ 1 A upperHalfPlaneSet) (g : SL(2, ℤ)) :
    ContDiffOn ℝ 1 (pull g A) upperHalfPlaneSet := by
  change ContDiffOn ℝ 1 (fun z ↦ A (mob g z) * ((starRingEnd ℂ (den g z)) ^ 2)⁻¹) _
  refine ContDiffOn.mul (hA.comp (contDiffOn_mob g) fun z hz ↦ im_mob_pos g hz) ?_
  refine ContDiffOn.inv (ContDiffOn.pow ?_ 2) fun z hz ↦
    pow_ne_zero 2 ((map_ne_zero _).2 (den_ne_zero g hz))
  exact (Complex.conjCLE.contDiff.comp_contDiffOn (contDiff_den g).contDiffOn)

theorem pull_mul_eq_of_mem {Γ : Subgroup SL(2, ℤ)} {A : ℂ → ℂ}
    (hinv : ∀ γ ∈ Γ, ∀ τ : ℍ, A ((γ • τ : ℍ) : ℂ) = (starRingEnd ℂ (denom γ τ)) ^ 2 * A τ)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (g : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    pull (γ * g) A z = pull g A z := by
  have h := pull_eq_self_of_mem hinv hγ (im_mob_pos g hz)
  rw [pull_mul γ g A hz]
  simp only [pull] at h ⊢
  rw [h]

theorem sideL_congr {B C : ℂ → ℂ} {H : ℝ} (hH : Real.sqrt 3 / 2 ≤ H)
    (h : ∀ z : ℂ, 0 < z.im → B z = C z) : sideL H B = sideL H C := by
  refine intervalIntegral.integral_congr fun y hy ↦ ?_
  rw [uIcc_of_le hH] at hy
  exact h _ (by rw [im_add_mul_I]; exact lt_of_lt_of_le sqrt3_half_pos hy.1)

theorem arc_congr {B C : ℂ → ℂ} (h : ∀ z : ℂ, 0 < z.im → B z = C z) : arc B = arc C := by
  refine intervalIntegral.integral_congr fun x hx ↦ ?_
  rw [uIcc_of_le (by norm_num)] at hx
  rw [h _ (by rw [im_add_mul_I]; exact arcHeight_pos (by nlinarith [hx.1, hx.2]))]

theorem sum_sideR_eq_sum_sideL {Γ : Subgroup SL(2, ℤ)} {R : Finset SL(2, ℤ)}
    (hR : Subgroup.IsComplement (Γ : Set SL(2, ℤ)) (R : Set SL(2, ℤ))) {A : ℂ → ℂ}
    (hinv : ∀ γ ∈ Γ, ∀ τ : ℍ, A ((γ • τ : ℍ) : ℂ) = (starRingEnd ℂ (denom γ τ)) ^ 2 * A τ)
    {H : ℝ} (hH : Real.sqrt 3 / 2 ≤ H) :
    ∑ g ∈ R, sideR H (pull g A) = ∑ g ∈ R, sideL H (pull g A) := by
  have e : ∀ g ∈ R, sideR H (pull g A) = sideL H (pull (g * ModularGroup.T) A) := fun g _ ↦ by
    rw [sideR_eq_sideL_pull_T]
    exact sideL_congr hH fun z hz ↦ (pull_mul g ModularGroup.T A hz).symm
  rw [Finset.sum_congr rfl e]
  exact sum_comp_mul_right hR ModularGroup.T (F := fun g ↦ sideL H (pull g A)) fun γ hγ g ↦
    sideL_congr hH fun z hz ↦ pull_mul_eq_of_mem hinv hγ g hz

theorem sum_arc_eq_zero {Γ : Subgroup SL(2, ℤ)} {R : Finset SL(2, ℤ)}
    (hR : Subgroup.IsComplement (Γ : Set SL(2, ℤ)) (R : Set SL(2, ℤ))) {A : ℂ → ℂ}
    (hinv : ∀ γ ∈ Γ, ∀ τ : ℍ, A ((γ • τ : ℍ) : ℂ) = (starRingEnd ℂ (denom γ τ)) ^ 2 * A τ) :
    ∑ g ∈ R, arc (pull g A) = 0 := by
  have e : ∀ g ∈ R, arc (pull (g * ModularGroup.S) A) = -arc (pull g A) := fun g _ ↦ by
    rw [← arc_pull_S]
    exact arc_congr fun z hz ↦ pull_mul g ModularGroup.S A hz
  have h2 : ∑ g ∈ R, arc (pull g A) = -∑ g ∈ R, arc (pull g A) :=
    calc ∑ g ∈ R, arc (pull g A) = ∑ g ∈ R, arc (pull (g * ModularGroup.S) A) :=
          (sum_comp_mul_right hR ModularGroup.S (F := fun g ↦ arc (pull g A)) fun γ hγ g ↦
            arc_congr fun z hz ↦ pull_mul_eq_of_mem hinv hγ g hz).symm
      _ = ∑ g ∈ R, -arc (pull g A) := Finset.sum_congr rfl e
      _ = -∑ g ∈ R, arc (pull g A) := Finset.sum_neg_distrib _
  linear_combination (1 / 2 : ℂ) * h2

theorem sum_integral_mob_tile_eq {Γ : Subgroup SL(2, ℤ)} {R : Finset SL(2, ℤ)}
    (hR : Subgroup.IsComplement (Γ : Set SL(2, ℤ)) (R : Set SL(2, ℤ))) {A : ℂ → ℂ}
    (hA : ContDiffOn ℝ 1 A upperHalfPlaneSet)
    (hinv : ∀ γ ∈ Γ, ∀ τ : ℍ, A ((γ • τ : ℍ) : ℂ) = (starRingEnd ℂ (denom γ τ)) ^ 2 * A τ)
    {H : ℝ} (hH : 1 ≤ H) :
    ∑ g ∈ R, ∫ z in mob g '' tile H, wirtinger A z =
      -(Complex.I / 2) * ∑ g ∈ R, cap H (pull g A) := by
  have e : ∀ g ∈ R, ∫ z in mob g '' tile H, wirtinger A z =
      (1 / 2 : ℂ) * (sideR H (pull g A) - sideL H (pull g A)) +
        (Complex.I / 2) * arc (pull g A) - (Complex.I / 2) * cap H (pull g A) := fun g _ ↦ by
    rw [integral_mob_tile hA g H, tile_stokes hH (contDiffOn_pull hA g)]
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib,
    sum_sideR_eq_sum_sideL hR hinv (sqrt3_half_le_one.trans hH), sum_arc_eq_zero hR hinv]
  ring

end MTT.Stokes

open MTT.Stokes in
theorem solution
    {Γ : Subgroup SL(2, ℤ)} {R : Finset SL(2, ℤ)}
    (hR : Subgroup.IsComplement (Γ : Set SL(2, ℤ)) (R : Set SL(2, ℤ)))
    {A : ℂ → ℂ} (hA : ContDiffOn ℝ 1 A upperHalfPlaneSet)
    (hinv : ∀ γ ∈ Γ, ∀ τ : ℍ, A ((γ • τ : ℍ) : ℂ) = (starRingEnd ℂ (denom γ τ)) ^ 2 * A τ)
    (hdecay : ∀ g : SL(2, ℤ), IsZeroAtImInfty
      fun τ : ℍ ↦ A ((g • τ : ℍ) : ℂ) * ((starRingEnd ℂ (denom g τ)) ^ 2)⁻¹)
    (hint : ∀ g ∈ R, IntegrableOn
      (fun z ↦ (1 / 2 : ℂ) * (fderiv ℝ A z 1 - Complex.I * fderiv ℝ A z Complex.I))
      ((fun τ : ℍ ↦ ((g • τ : ℍ) : ℂ)) '' 𝒟) volume) :
    ∑ g ∈ R, ∫ z in (fun τ : ℍ ↦ ((g • τ : ℍ) : ℂ)) '' 𝒟,
      (1 / 2 : ℂ) * (fderiv ℝ A z 1 - Complex.I * fderiv ℝ A z Complex.I) = 0 := by
  have hint' : ∀ g ∈ R, IntegrableOn (wirtinger A) (mob g '' (UpperHalfPlane.coe '' 𝒟)) :=
    fun g hg ↦ by
      have := hint g hg
      rwa [image_coe_fd_eq] at this
  have key : (∑ g ∈ R, ∫ z in (fun τ : ℍ ↦ ((g • τ : ℍ) : ℂ)) '' 𝒟,
      (1 / 2 : ℂ) * (fderiv ℝ A z 1 - Complex.I * fderiv ℝ A z Complex.I)) =
      ∑ g ∈ R, ∫ z in mob g '' (UpperHalfPlane.coe '' 𝒟), wirtinger A z :=
    Finset.sum_congr rfl fun g _ ↦ by rw [image_coe_fd_eq]; rfl
  have hlim1 : Tendsto (fun H : ℝ ↦ ∑ g ∈ R, ∫ z in mob g '' tile H, wirtinger A z) atTop
      (𝓝 (∑ g ∈ R, ∫ z in mob g '' (UpperHalfPlane.coe '' 𝒟), wirtinger A z)) :=
    tendsto_finsetSum _ fun g hg ↦ tendsto_integral_mob_tile g (hint' g hg)
  have hlim2 : Tendsto (fun H : ℝ ↦ ∑ g ∈ R, ∫ z in mob g '' tile H, wirtinger A z) atTop
      (𝓝 0) := by
    have h := (tendsto_finsetSum R fun g _ ↦ tendsto_cap g (hdecay g)).const_mul
      (-(Complex.I / 2))
    simp only [Finset.sum_const_zero, mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with H hH
    exact (sum_integral_mob_tile_eq hR hA hinv hH).symm
  rw [key]
  exact tendsto_nhds_unique hlim1 hlim2

end privateSection

public section publicSection

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Modular

theorem MTT.sum_integral_wirtinger_smul_fd_eq_zero
    {Γ : Subgroup SL(2, ℤ)} {R : Finset SL(2, ℤ)}
    (hR : Subgroup.IsComplement (Γ : Set SL(2, ℤ)) (R : Set SL(2, ℤ)))
    {A : ℂ → ℂ} (hA : ContDiffOn ℝ 1 A upperHalfPlaneSet)
    (hinv : ∀ γ ∈ Γ, ∀ τ : ℍ, A ((γ • τ : ℍ) : ℂ) = (starRingEnd ℂ (denom γ τ)) ^ 2 * A τ)
    (hdecay : ∀ g : SL(2, ℤ), IsZeroAtImInfty
      fun τ : ℍ ↦ A ((g • τ : ℍ) : ℂ) * ((starRingEnd ℂ (denom g τ)) ^ 2)⁻¹)
    (hint : ∀ g ∈ R, IntegrableOn
      (fun z ↦ (1 / 2 : ℂ) * (fderiv ℝ A z 1 - Complex.I * fderiv ℝ A z Complex.I))
      ((fun τ : ℍ ↦ ((g • τ : ℍ) : ℂ)) '' 𝒟) volume) :
    ∑ g ∈ R, ∫ z in (fun τ : ℍ ↦ ((g • τ : ℍ) : ℂ)) '' 𝒟,
      (1 / 2 : ℂ) * (fderiv ℝ A z 1 - Complex.I * fderiv ℝ A z Complex.I) = 0 :=
  solution hR hA hinv hdecay hint

end publicSection
