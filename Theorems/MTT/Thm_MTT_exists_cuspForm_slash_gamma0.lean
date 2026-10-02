module

public import Definitions.MTT.Def_MTT_Arithmetic

noncomputable section privateSection

open scoped BigOperators ModularForm MatrixGroups Pointwise
open UpperHalfPlane Matrix CongruenceSubgroup

namespace MTT.HeckePort

/-! ### Integer matrices as elements of `GL₂(ℚ)` and `GL₂(ℝ)` -/

/-- An integer matrix viewed in `GL₂(ℚ)` (junk value `1` if the determinant vanishes). -/
def toGLQ (A : Matrix (Fin 2) (Fin 2) ℤ) : GL (Fin 2) ℚ :=
  if h : ((Int.castRingHom ℚ).mapMatrix A).det ≠ 0 then
    Matrix.GeneralLinearGroup.mkOfDetNeZero _ h else 1

/-- An integer matrix viewed in `GL₂(ℝ)`, through `GL₂(ℚ)`. -/
def toGL (A : Matrix (Fin 2) (Fin 2) ℤ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (toGLQ A)

lemma det_map_ne_zero {A : Matrix (Fin 2) (Fin 2) ℤ} (h : A.det ≠ 0) :
    ((Int.castRingHom ℚ).mapMatrix A).det ≠ 0 := by
  rw [← RingHom.map_det]; simpa using h

lemma toGLQ_val {A : Matrix (Fin 2) (Fin 2) ℤ} (h : A.det ≠ 0) :
    (toGLQ A : Matrix (Fin 2) (Fin 2) ℚ) = (Int.castRingHom ℚ).mapMatrix A := by
  rw [toGLQ, dite_eq_left (det_map_ne_zero h)]; rfl

lemma toGL_apply {A : Matrix (Fin 2) (Fin 2) ℤ} (h : A.det ≠ 0) (i j : Fin 2) :
    (toGL A : Matrix (Fin 2) (Fin 2) ℝ) i j = (A i j : ℝ) := by
  rw [toGL, Matrix.GeneralLinearGroup.map_apply, toGLQ_val h]
  simp

lemma toGL_det_matrix {A : Matrix (Fin 2) (Fin 2) ℤ} (h : A.det ≠ 0) :
    (toGL A : Matrix (Fin 2) (Fin 2) ℝ).det = (A.det : ℝ) := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [toGL_apply h]
  push_cast; ring

lemma toGL_det {A : Matrix (Fin 2) (Fin 2) ℤ} (h : A.det ≠ 0) :
    (Matrix.GeneralLinearGroup.det (toGL A) : ℝ) = (A.det : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, toGL_det_matrix h]

lemma toGL_mul {A B : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    toGL (A * B) = toGL A * toGL B := by
  have hAB : (A * B).det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero hA hB
  ext i j
  rw [Units.val_mul, Matrix.mul_apply, toGL_apply hAB, Matrix.mul_apply]
  simp only [toGL_apply hA, toGL_apply hB]
  push_cast; rfl

lemma toGL_SL (γ : SL(2, ℤ)) :
    toGL (γ : Matrix (Fin 2) (Fin 2) ℤ) = Matrix.SpecialLinearGroup.mapGL ℝ γ := by
  ext i j
  rw [toGL_apply (by simp), Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  simp

lemma toGL_det_pos {A : Matrix (Fin 2) (Fin 2) ℤ} (h : 0 < A.det) :
    0 < (Matrix.GeneralLinearGroup.det (toGL A) : ℝ) := by
  rw [toGL_det h.ne']; exact_mod_cast h

lemma σ_toGL {A : Matrix (Fin 2) (Fin 2) ℤ} (h : 0 < A.det) (z : ℂ) : σ (toGL A) z = z := by
  simp [σ, toGL_det_matrix h.ne', h]

lemma coe_toGL_smul {A : Matrix (Fin 2) (Fin 2) ℤ} (h : 0 < A.det) (τ : ℍ) :
    ((toGL A • τ : ℍ) : ℂ) =
      ((A 0 0 : ℂ) * τ + (A 0 1 : ℂ)) / ((A 1 0 : ℂ) * τ + (A 1 1 : ℂ)) := by
  rw [coe_smul_of_det_pos (toGL_det_pos h)]
  simp [num, denom, toGL_apply h.ne']

lemma slash_toGL_apply {A : Matrix (Fin 2) (Fin 2) ℤ} (h : 0 < A.det) (k : ℤ) (f : ℍ → ℂ)
    (τ : ℍ) :
    (f ∣[k] toGL A) τ =
      f (toGL A • τ) * (A.det : ℂ) ^ (k - 1) *
        ((A 1 0 : ℂ) * τ + (A 1 1 : ℂ)) ^ (-k) := by
  rw [ModularForm.slash_apply, σ_toGL h, toGL_det h.ne', abs_of_pos (by exact_mod_cast h)]
  simp [denom, toGL_apply h.ne']

lemma slash_mapGL_apply (γ : SL(2, ℤ)) (k : ℤ) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ γ) τ =
      f (Matrix.SpecialLinearGroup.mapGL ℝ γ • τ) *
        (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ (-k) := by
  rw [← toGL_SL, slash_toGL_apply (by simp)]
  simp

lemma denom_SL_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) :
    ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
  have := denom_ne_zero (toGL (γ : Matrix (Fin 2) (Fin 2) ℤ)) τ
  simpa [denom, toGL_apply (show (γ : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 by simp)] using this


variable {N : ℕ}

/-- Rational matrices preserve the cusps of `Γ₁(N)`. -/
lemma isCusp_toGL_smul (hN : 0 < N) {c : OnePoint ℝ} (hc : IsCusp c (MTT.GammaOne N))
    (A : Matrix (Fin 2) (Fin 2) ℤ) : IsCusp (toGL A • c) (MTT.GammaOne N) := by
  have : NeZero N := ⟨hN.ne'⟩
  have h1 := hc.smul (toGL A)
  have h2 : (ConjAct.toConjAct (toGL A) • (MTT.GammaOne N)).IsArithmetic :=
    Subgroup.IsArithmetic.conj (MTT.GammaOne N) (toGLQ A)
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at h1 ⊢
  exact h1


/-- `Γ₁(N)` is normal in `Γ₀(N)`. -/
lemma conj_mem_Gamma1 (γ : Gamma0 N) {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma1 N) :
    γ.val * δ * γ.val⁻¹ ∈ Gamma1 N := by
  rw [Gamma1, Subgroup.mem_map] at hδ ⊢
  obtain ⟨δ', -, rfl⟩ := hδ
  refine ⟨⟨γ * δ'.val * γ⁻¹, ?_⟩, Subgroup.mem_top _, ?_⟩
  · exact (MonoidHom.normal_ker (Gamma0Map N)).conj_mem δ'.val δ'.property γ
  · simp

/-- The slash of a cusp form on `Γ₁(N)` by an element of `Γ₀(N)`. -/
def slashCuspForm (hN : 0 < N) {k : ℕ} (g : CuspForm (MTT.GammaOne N) (k : ℤ)) (γ : Gamma0 N) :
    CuspForm (MTT.GammaOne N) (k : ℤ) where
  toFun := (g : ℍ → ℂ) ∣[(k : ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ γ.val
  slash_action_eq' := by
    rintro δ ⟨δ₀, hδ₀, rfl⟩
    have hmem : γ.val * δ₀ * γ.val⁻¹ ∈ Gamma1 N := conj_mem_Gamma1 γ hδ₀
    rw [← SlashAction.slash_mul, ← map_mul,
      show γ.val * δ₀ = (γ.val * δ₀ * γ.val⁻¹) * γ.val by group,
      map_mul, SlashAction.slash_mul,
      SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩)]
  holo' := (ModularFormClass.holo g).slash _ _
  zero_at_cusps' := by
    intro c hc h hh
    rw [← SlashAction.slash_mul]
    have hc' : IsCusp (Matrix.SpecialLinearGroup.mapGL ℝ γ.val • c) (MTT.GammaOne N) := by
      rw [← toGL_SL]; exact isCusp_toGL_smul hN hc _
    exact CuspFormClass.zero_at_cusps g hc' (Matrix.SpecialLinearGroup.mapGL ℝ γ.val * h)
      (by rw [mul_smul, hh])

theorem exists_cuspForm_slash_gamma0
    (hN : 0 < N) {k : ℕ} (g : CuspForm (MTT.GammaOne N) (k : ℤ))
    (γ : Gamma0 N) :
    ∃ g' : CuspForm (MTT.GammaOne N) (k : ℤ), ∀ z : ℍ,
      g ((Matrix.SpecialLinearGroup.mapGL ℝ γ.val) • z) =
        (((γ.val 1 0 : ℤ) : ℂ) * z + ((γ.val 1 1 : ℤ) : ℂ)) ^ k * g' z := by
  refine ⟨slashCuspForm hN g γ, fun z => ?_⟩
  change _ = _ * ((g : ℍ → ℂ) ∣[(k : ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ γ.val) z
  rw [slash_mapGL_apply, zpow_neg, zpow_natCast]
  have hd := denom_SL_ne_zero γ.val z
  field_simp

end MTT.HeckePort

theorem solution
    {N k : ℕ} (hN : 0 < N) (g : CuspForm (MTT.GammaOne N) (k : ℤ))
    (γ : CongruenceSubgroup.Gamma0 N) :
    ∃ g' : CuspForm (MTT.GammaOne N) (k : ℤ), ∀ z : UpperHalfPlane,
      g ((Matrix.SpecialLinearGroup.mapGL ℝ γ.val) • z) =
        (((γ.val 1 0 : ℤ) : ℂ) * z + ((γ.val 1 1 : ℤ) : ℂ)) ^ k * g' z :=
  MTT.HeckePort.exists_cuspForm_slash_gamma0 hN g γ

end privateSection

public noncomputable section publicSection

open scoped BigOperators

theorem MTT.exists_cuspForm_slash_gamma0
    {N k : ℕ} (hN : 0 < N) (g : CuspForm (MTT.GammaOne N) (k : ℤ))
    (γ : CongruenceSubgroup.Gamma0 N) :
    ∃ g' : CuspForm (MTT.GammaOne N) (k : ℤ), ∀ z : UpperHalfPlane,
      g ((Matrix.SpecialLinearGroup.mapGL ℝ γ.val) • z) =
        (((γ.val 1 0 : ℤ) : ℂ) * z + ((γ.val 1 1 : ℤ) : ℂ)) ^ k * g' z :=
  solution hN g γ

end publicSection
