import Definitions.MTT.Def_MTT_Arithmetic
import Mathlib.Algebra.Field.ZMod
set_option autoImplicit false
noncomputable section
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
      f (toGL A • τ) * (A.det : ℂ) ^ (k - 1) * ((A 1 0 : ℂ) * τ + (A 1 1 : ℂ)) ^ (-k) := by
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

/-! ### The nebentype law in slash form -/

variable {N : ℕ}

lemma slash_of_law {k : ℕ} (e : DirichletCharacter ℂ N) (g : ℍ → ℂ)
    (hg : ∀ γ : Gamma0 N, ∀ z : ℍ, g (Matrix.SpecialLinearGroup.mapGL ℝ γ.val • z) =
      e (γ.val 1 1 : ZMod N) * (((γ.val 1 0 : ℤ) : ℂ) * z + ((γ.val 1 1 : ℤ) : ℂ)) ^ k * g z)
    (γ : Gamma0 N) :
    g ∣[(k : ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ γ.val = e (γ.val 1 1 : ZMod N) • g := by
  funext τ
  rw [slash_mapGL_apply, hg γ τ, Pi.smul_apply, smul_eq_mul, zpow_neg, zpow_natCast]
  have hd := denom_SL_ne_zero γ.val τ
  field_simp

lemma law_of_slash {k : ℕ} (e : DirichletCharacter ℂ N) (g : ℍ → ℂ) (γ : Gamma0 N)
    (h : g ∣[(k : ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ γ.val = e (γ.val 1 1 : ZMod N) • g)
    (z : ℍ) :
    g (Matrix.SpecialLinearGroup.mapGL ℝ γ.val • z) =
      e (γ.val 1 1 : ZMod N) * (((γ.val 1 0 : ℤ) : ℂ) * z + ((γ.val 1 1 : ℤ) : ℂ)) ^ k * g z := by
  have := congrFun h z
  rw [slash_mapGL_apply, Pi.smul_apply, smul_eq_mul, zpow_neg, zpow_natCast] at this
  have hd := denom_SL_ne_zero γ.val z
  calc g (Matrix.SpecialLinearGroup.mapGL ℝ γ.val • z)
      = g (Matrix.SpecialLinearGroup.mapGL ℝ γ.val • z) *
          ((((γ.val 1 0 : ℤ) : ℂ) * z + ((γ.val 1 1 : ℤ) : ℂ)) ^ k)⁻¹ *
          (((γ.val 1 0 : ℤ) : ℂ) * z + ((γ.val 1 1 : ℤ) : ℂ)) ^ k := by
        field_simp
    _ = _ := by rw [this]; ring

/-! ### The matrices `β_b = [1 b; 0 l]` and `α = [l 0; 0 1]` -/

variable (l : ℕ)

def β (b : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, (b : ℤ); 0, (l : ℤ)]
def α : Matrix (Fin 2) (Fin 2) ℤ := !![(l : ℤ), 0; 0, 1]

@[simp] lemma det_β (b : ℕ) : (β l b).det = l := by simp [β, Matrix.det_fin_two_of]
@[simp] lemma det_α : (α l).det = l := by simp [α, Matrix.det_fin_two_of]

/-- The coset representatives, indexed by `P¹(F_l) = F_l ∪ {∞}`. -/
def Mx : Option (ZMod l) → Matrix (Fin 2) (Fin 2) ℤ
  | none => α l
  | some b => β l b.val

@[simp] lemma Mx_none : Mx l none = α l := rfl
@[simp] lemma Mx_some (b : ZMod l) : Mx l (some b) = β l b.val := rfl

lemma det_Mx (x : Option (ZMod l)) : (Mx l x).det = l := by cases x <;> simp

/-- The coefficients: `1` on the `β_b`, `ε(l)` on `α`. -/
def cx (e : DirichletCharacter ℂ N) : Option (ZMod l) → ℂ
  | none => e l
  | some _ => 1

@[simp] lemma cx_none (e : DirichletCharacter ℂ N) : cx l e none = e l := rfl
@[simp] lemma cx_some (e : DirichletCharacter ℂ N) (b : ZMod l) : cx l e (some b) = 1 := rfl

variable {l} [hl : Fact l.Prime]

lemma det_Mx_pos (x : Option (ZMod l)) : 0 < (Mx l x).det := by
  rw [det_Mx]; exact_mod_cast hl.out.pos

lemma l_pos : 0 < (l : ℤ) := by exact_mod_cast hl.out.pos

/-- The Hecke operator `T_l` (or `U_l`) as a sum of slashes. -/
def T (e : DirichletCharacter ℂ N) (k : ℤ) (g : ℍ → ℂ) : ℍ → ℂ :=
  ∑ x : Option (ZMod l), cx l e x • (g ∣[k] toGL (Mx l x))

lemma im_shift_div_pos (τ : ℍ) (b : ℕ) : 0 < (((τ : ℂ) + (b : ℂ)) / (l : ℂ)).im := by
  rw [Complex.div_natCast_im, Complex.add_im, Complex.natCast_im, add_zero]
  exact div_pos τ.im_pos (Nat.cast_pos.mpr hl.out.pos)

lemma im_mul_pos (τ : ℍ) : 0 < ((l : ℂ) * (τ : ℂ)).im := by
  simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
  exact mul_pos (Nat.cast_pos.mpr hl.out.pos) τ.im_pos

lemma toGL_β_smul (b : ℕ) (τ : ℍ) :
    toGL (β l b) • τ = ofComplex (((τ : ℂ) + (b : ℂ)) / (l : ℂ)) := by
  have hpos : 0 < (β l b).det := by rw [det_β]; exact l_pos
  apply UpperHalfPlane.ext
  rw [coe_toGL_smul hpos, ofComplex_apply_of_im_pos (im_shift_div_pos τ b)]
  simp [β]

lemma toGL_α_smul (τ : ℍ) : toGL (α l) • τ = ofComplex ((l : ℂ) * (τ : ℂ)) := by
  have hpos : 0 < (α l).det := by rw [det_α]; exact l_pos
  apply UpperHalfPlane.ext
  rw [coe_toGL_smul hpos, ofComplex_apply_of_im_pos (im_mul_pos τ)]
  simp [α]

lemma slash_β_apply (k : ℤ) (g : ℍ → ℂ) (b : ℕ) (τ : ℍ) :
    (g ∣[k] toGL (β l b)) τ = (l : ℂ)⁻¹ * g (ofComplex (((τ : ℂ) + (b : ℂ)) / (l : ℂ))) := by
  have hpos : 0 < (β l b).det := by rw [det_β]; exact l_pos
  have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  rw [slash_toGL_apply hpos, toGL_β_smul, det_β]
  simp only [β, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.empty_val', Matrix.cons_val_fin_one, Int.cast_zero, zero_mul,
    zero_add, Int.cast_natCast]
  rw [mul_assoc, ← zpow_add₀ hl0, show k - 1 + -k = -1 by ring, zpow_neg_one, mul_comm]

lemma slash_α_apply (k : ℤ) (g : ℍ → ℂ) (τ : ℍ) :
    (g ∣[k] toGL (α l)) τ = (l : ℂ) ^ (k - 1) * g (ofComplex ((l : ℂ) * (τ : ℂ))) := by
  have hpos : 0 < (α l).det := by rw [det_α]; exact l_pos
  rw [slash_toGL_apply hpos, toGL_α_smul, det_α]
  simp only [α, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.empty_val', Matrix.cons_val_fin_one, Int.cast_zero, zero_mul,
    zero_add, Int.cast_one, one_zpow, mul_one, Int.cast_natCast]
  ring

/-- `Fin l ≃ ZMod l`, preserving `val`. -/
def finEquivZMod : Fin l ≃ ZMod l where
  toFun i := (i.val : ZMod l)
  invFun z := ⟨z.val, z.val_lt⟩
  left_inv i := by ext; simp [ZMod.val_natCast, Nat.mod_eq_of_lt i.2]
  right_inv z := by simp

lemma finEquivZMod_val (i : Fin l) : (finEquivZMod i : ZMod l).val = i.val := by
  simp [finEquivZMod, ZMod.val_natCast, Nat.mod_eq_of_lt i.2]

/-- The slash-sum operator agrees pointwise with the mission's `heckePrime` (for `k ≥ 1`). -/
lemma T_apply (e : DirichletCharacter ℂ N) {k : ℕ} (hk : 1 ≤ k) (g : ℍ → ℂ) (τ : ℍ) :
    T (l := l) e (k : ℤ) g τ = MTT.heckePrime k (e l) l g τ := by
  unfold T
  rw [Finset.sum_apply, Fintype.sum_option]
  simp only [Pi.smul_apply, Mx_none, Mx_some, cx_none, cx_some, smul_eq_mul, one_mul]
  simp only [slash_α_apply (l := l)]
  simp only [slash_β_apply (l := l)]
  simp only [MTT.heckePrime]
  rw [add_comm]
  congr 1
  · rw [Finset.mul_sum]
    refine Fintype.sum_equiv (finEquivZMod (l := l)).symm
      (fun z : ZMod l => (l : ℂ)⁻¹ * g (ofComplex (((τ : ℂ) + (z.val : ℂ)) / (l : ℂ))))
      (fun i : Fin l => (l : ℂ)⁻¹ * g (ofComplex (((τ : ℂ) + (i.val : ℂ)) / (l : ℂ))))
      (fun z => ?_)
    rfl
  · rw [show ((k : ℤ) - 1) = ((k - 1 : ℕ) : ℤ) by omega, zpow_natCast]
    ring

/-! ### The Möbius permutation of `P¹(F_l)` -/

section moebius
variable {K : Type*} [Field K] [DecidableEq K]

/-- The action of `[A B; C D]` on `P¹(K) = K ∪ {∞}` by `t ↦ (B + tD)/(A + tC)`. -/
def mob (A B C D : K) : Option K → Option K
  | none => if C = 0 then none else some (D / C)
  | some t => if A + t * C = 0 then none else some ((B + t * D) / (A + t * C))

lemma mob_injective (A B C D : K) (h : A * D - B * C = 1) :
    Function.Injective (mob A B C D) := by
  intro x y hxy
  rcases x with _ | t <;> rcases y with _ | s
  · rfl
  · exfalso
    by_cases hC : C = 0
    · simp only [mob, ite_eq_left hC] at hxy
      split_ifs at hxy with hs
      all_goals first
        | exact Option.noConfusion hxy
        | (rw [hC, mul_zero, add_zero] at hs; rw [hs, hC] at h; simp at h)
    · by_cases hs : A + s * C = 0
      · simp [mob, hC, hs] at hxy
      · simp only [mob, ite_eq_right hC, ite_eq_right hs, Option.some.injEq] at hxy
        rw [div_eq_div_iff hC hs] at hxy
        have : A * D - B * C = 0 := by linear_combination hxy
        rw [h] at this; exact one_ne_zero this
  · exfalso
    by_cases hC : C = 0
    · simp only [mob, ite_eq_left hC] at hxy
      split_ifs at hxy with ht
      all_goals first
        | exact Option.noConfusion hxy
        | (rw [hC, mul_zero, add_zero] at ht; rw [ht, hC] at h; simp at h)
    · by_cases ht : A + t * C = 0
      · simp [mob, hC, ht] at hxy
      · simp only [mob, ite_eq_right hC, ite_eq_right ht, Option.some.injEq] at hxy
        rw [div_eq_div_iff ht hC] at hxy
        have : A * D - B * C = 0 := by linear_combination -hxy
        rw [h] at this; exact one_ne_zero this
  · by_cases ht : A + t * C = 0
    · by_cases hs : A + s * C = 0
      · by_cases hC : C = 0
        · exfalso; rw [hC, mul_zero, add_zero] at ht; rw [ht, hC] at h; simp at h
        · have : (t - s) * C = 0 := by linear_combination ht - hs
          rcases mul_eq_zero.mp this with h1 | h1
          · rw [sub_eq_zero.mp h1]
          · exact absurd h1 hC
      · exfalso; simp [mob, ht, hs] at hxy
    · by_cases hs : A + s * C = 0
      · exfalso; simp [mob, ht, hs] at hxy
      · simp only [mob, ite_eq_right ht, ite_eq_right hs, Option.some.injEq] at hxy
        rw [div_eq_div_iff ht hs] at hxy
        have : (t - s) * (A * D - B * C) = 0 := by linear_combination hxy
        rw [h, mul_one] at this
        rw [sub_eq_zero.mp this]

end moebius

/-! ### The permutation argument -/

lemma det_entries (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := γ.2; rwa [Matrix.det_fin_two] at this

section key

/-- The permutation of `P¹(F_l)` induced by `γ ∈ Γ₀(N)`. -/
def σγ (γ : Gamma0 N) : Option (ZMod l) → Option (ZMod l) :=
  mob ((γ.val 0 0 : ℤ) : ZMod l) ((γ.val 0 1 : ℤ) : ZMod l)
    ((γ.val 1 0 : ℤ) : ZMod l) ((γ.val 1 1 : ℤ) : ZMod l)

lemma σγ_injective (γ : Gamma0 N) : Function.Injective (σγ (l := l) γ) := by
  apply mob_injective
  have := congrArg (Int.cast : ℤ → ZMod l) (det_entries γ.val)
  push_cast at this
  exact this

/-- Build an element of `Γ₀(N)` from a matrix of determinant one. -/
def mkGamma0 (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = 1) (hc : (M 1 0 : ZMod N) = 0) :
    Gamma0 N :=
  ⟨⟨M, hdet⟩, Gamma0_mem.mpr hc⟩

@[simp] lemma mkGamma0_coe (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = 1)
    (hc : (M 1 0 : ZMod N) = 0) :
    ((mkGamma0 M hdet hc).val : Matrix (Fin 2) (Fin 2) ℤ) = M := rfl

lemma slash_factor (e : DirichletCharacter ℂ N) {k : ℤ} (g : ℍ → ℂ) (γ : Gamma0 N)
    (hg : ∀ γ' : Gamma0 N, g ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ γ'.val =
      e (γ'.val 1 1 : ZMod N) • g)
    (x y : Option (ZMod l)) (γ' : Gamma0 N)
    (hfac : Mx l x * (γ.val : Matrix (Fin 2) (Fin 2) ℤ) =
      (γ'.val : Matrix (Fin 2) (Fin 2) ℤ) * Mx l y) :
    g ∣[k] toGL (Mx l x * (γ.val : Matrix (Fin 2) (Fin 2) ℤ)) =
      e (γ'.val 1 1 : ZMod N) • (g ∣[k] toGL (Mx l y)) := by
  rw [hfac, toGL_mul (by simp) (det_Mx_pos y).ne', toGL_SL, SlashAction.slash_mul, hg γ',
    ModularForm.smul_slash, σ_toGL (det_Mx_pos y)]

lemma cast_val_eq (b : ZMod l) : ((b.val : ℤ) : ZMod l) = b := by
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

/-- The matrix identity for the four kinds of cosets. -/
lemma key (e : DirichletCharacter ℂ N) {k : ℤ} (g : ℍ → ℂ)
    (hg : ∀ γ' : Gamma0 N, g ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ γ'.val =
      e (γ'.val 1 1 : ZMod N) • g)
    (γ : Gamma0 N) (x : Option (ZMod l)) :
    cx l e x • (g ∣[k] toGL (Mx l x * (γ.val : Matrix (Fin 2) (Fin 2) ℤ))) =
      (e (γ.val 1 1 : ZMod N) * cx l e (σγ γ x)) • (g ∣[k] toGL (Mx l (σγ γ x))) := by
  have hdet := det_entries γ.val
  have hcN : ((γ.val 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.mp γ.2
  rcases x with _ | b₀
  · -- the coset of `α = [l 0; 0 1]`
    by_cases hc0 : ((γ.val 1 0 : ℤ) : ZMod l) = 0
    · have hσ : σγ (l := l) γ none = none := by simp [σγ, mob, hc0]
      rw [hσ]
      by_cases hlN : l ∣ N
      · have h0 : e (l : ZMod N) = 0 := MulChar.map_nonunit e (by
          rw [ZMod.isUnit_iff_coprime]
          exact fun h => hl.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd h hlN))
        simp [h0]
      · have hlc : (l : ℤ) ∣ γ.val 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ l).mp hc0
        have hcop : IsCoprime (N : ℤ) (l : ℤ) :=
          Nat.isCoprime_iff_coprime.mpr ((hl.out.coprime_iff_not_dvd.mpr hlN).symm)
        have hNc : (N : ℤ) ∣ γ.val 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hcN
        have hcl : (l : ℤ) * (γ.val 1 0 / l) = γ.val 1 0 := Int.mul_ediv_cancel' hlc
        have hNcl : (N : ℤ) ∣ γ.val 1 0 / l := by
          apply hcop.dvd_of_dvd_mul_left
          rw [hcl]; exact hNc
        let γ' : Gamma0 N := mkGamma0 !![γ.val 0 0, l * γ.val 0 1; γ.val 1 0 / l, γ.val 1 1]
          (by rw [Matrix.det_fin_two_of]; linear_combination hdet - γ.val 0 1 * hcl)
          (by simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr hNcl)
        rw [slash_factor e g γ hg none none γ' (by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [-ZMod.natCast_val, Mx, α, γ', mkGamma0, Matrix.mul_apply, Fin.sum_univ_two] <;>
            first | ring1 | linear_combination hcl | linear_combination -hcl)]
        simp only [cx_none, smul_smul]
        congr 1
        simp [γ', mkGamma0, mul_comm]
    · set b' : ZMod l := ((γ.val 1 1 : ℤ) : ZMod l) / ((γ.val 1 0 : ℤ) : ZMod l) with hb'
      have hσ : σγ (l := l) γ none = some b' := by simp [σγ, mob, hc0, hb']
      rw [hσ]
      have hdiv : (l : ℤ) ∣ γ.val 1 1 - γ.val 1 0 * b'.val := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val, hb']
        field_simp
        ring
      set d' : ℤ := (γ.val 1 1 - γ.val 1 0 * b'.val) / l with hd'
      have hld' : (l : ℤ) * d' = γ.val 1 1 - γ.val 1 0 * b'.val := Int.mul_ediv_cancel' hdiv
      let γ' : Gamma0 N :=
        mkGamma0 !![l * γ.val 0 0, γ.val 0 1 - γ.val 0 0 * b'.val; γ.val 1 0, d']
          (by rw [Matrix.det_fin_two_of]; linear_combination hdet + γ.val 0 0 * hld')
          (by simpa using hcN)
      rw [slash_factor e g γ hg none (some b') γ' (by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [-ZMod.natCast_val, Mx, α, β, γ', mkGamma0, Matrix.mul_apply, Fin.sum_univ_two] <;>
          first | ring1 | linear_combination hld' | linear_combination -hld')]
      simp only [cx_none, cx_some, smul_smul, mul_one]
      congr 1
      simp only [γ', mkGamma0_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one]
      rw [← map_mul]
      congr 1
      have := congrArg (Int.cast : ℤ → ZMod N) hld'
      push_cast at this
      simp [this, hcN]
  · -- the coset of `β_{b₀} = [1 b₀; 0 l]`
    by_cases hu : ((γ.val 0 0 : ℤ) : ZMod l) + b₀ * ((γ.val 1 0 : ℤ) : ZMod l) = 0
    · have hσ : σγ (l := l) γ (some b₀) = none := by simp [σγ, mob, hu]
      rw [hσ]
      have hdiv : (l : ℤ) ∣ γ.val 0 0 + b₀.val * γ.val 1 0 := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [ZMod.natCast_zmod_val]; exact hu
      set u' : ℤ := (γ.val 0 0 + b₀.val * γ.val 1 0) / l with hu'
      have hlu : (l : ℤ) * u' = γ.val 0 0 + b₀.val * γ.val 1 0 := Int.mul_ediv_cancel' hdiv
      let γ' : Gamma0 N :=
        mkGamma0 !![u', γ.val 0 1 + b₀.val * γ.val 1 1; γ.val 1 0, l * γ.val 1 1]
          (by rw [Matrix.det_fin_two_of]; linear_combination hdet + γ.val 1 1 * hlu)
          (by simpa using hcN)
      rw [slash_factor e g γ hg (some b₀) none γ' (by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [-ZMod.natCast_val, Mx, α, β, γ', mkGamma0, Matrix.mul_apply, Fin.sum_univ_two] <;>
          first | ring1 | linear_combination hlu | linear_combination -hlu)]
      simp only [cx_none, cx_some, smul_smul, one_mul]
      congr 1
      simp only [γ', mkGamma0_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one]
      push_cast
      rw [map_mul, mul_comm]
    · set b' : ZMod l := (((γ.val 0 1 : ℤ) : ZMod l) + b₀ * ((γ.val 1 1 : ℤ) : ZMod l)) /
          (((γ.val 0 0 : ℤ) : ZMod l) + b₀ * ((γ.val 1 0 : ℤ) : ZMod l)) with hb'
      have hσ : σγ (l := l) γ (some b₀) = some b' := by simp [σγ, mob, hu, hb']
      rw [hσ]
      have hdiv : (l : ℤ) ∣ (γ.val 0 1 + b₀.val * γ.val 1 1) -
          (γ.val 0 0 + b₀.val * γ.val 1 0) * b'.val := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        simp only [ZMod.natCast_zmod_val]
        rw [hb']
        field_simp
        ring
      set q : ℤ := ((γ.val 0 1 + b₀.val * γ.val 1 1) -
          (γ.val 0 0 + b₀.val * γ.val 1 0) * b'.val) / l with hq
      have hlq : (l : ℤ) * q = (γ.val 0 1 + b₀.val * γ.val 1 1) -
          (γ.val 0 0 + b₀.val * γ.val 1 0) * b'.val := Int.mul_ediv_cancel' hdiv
      let γ' : Gamma0 N :=
        mkGamma0 !![γ.val 0 0 + b₀.val * γ.val 1 0, q; l * γ.val 1 0, γ.val 1 1 - γ.val 1 0 * b'.val]
          (by rw [Matrix.det_fin_two_of]; linear_combination hdet - γ.val 1 0 * hlq)
          (by simp [hcN])
      rw [slash_factor e g γ hg (some b₀) (some b') γ' (by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [-ZMod.natCast_val, Mx, β, γ', mkGamma0, Matrix.mul_apply, Fin.sum_univ_two] <;>
          first | ring1 | linear_combination hlq | linear_combination -hlq)]
      simp only [cx_some, smul_smul, one_mul, mul_one]
      congr 1
      simp only [γ', mkGamma0_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one]
      push_cast
      simp [hcN]

end key

/-! ### Assembly: the Γ₀(N)-law, the cusp condition, and the cusp form `T_l g` -/

section assemble
variable {l : ℕ} [hl : Fact l.Prime]

lemma σ_SL (γ : SL(2, ℤ)) (z : ℂ) : σ (Matrix.SpecialLinearGroup.mapGL ℝ γ) z = z := by
  rw [← toGL_SL]; exact σ_toGL (by simp) z

/-- The Γ₀(N)-law for the slash-sum operator. -/
lemma T_slash (e : DirichletCharacter ℂ N) {k : ℤ} (g : ℍ → ℂ)
    (hg : ∀ γ' : Gamma0 N, g ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ γ'.val =
      e (γ'.val 1 1 : ZMod N) • g) (γ : Gamma0 N) :
    T (l := l) e k g ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ γ.val =
      e (γ.val 1 1 : ZMod N) • T (l := l) e k g := by
  unfold T
  rw [SlashAction.sum_slash, Finset.smul_sum]
  have hbij : Function.Bijective (σγ (l := l) γ) :=
    Finite.injective_iff_bijective.mp (σγ_injective γ)
  let σe : Option (ZMod l) ≃ Option (ZMod l) := Equiv.ofBijective _ hbij
  calc ∑ x, (cx l e x • (g ∣[k] toGL (Mx l x))) ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ γ.val
      = ∑ x, (e (γ.val 1 1 : ZMod N) * cx l e (σγ γ x)) • (g ∣[k] toGL (Mx l (σγ γ x))) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [ModularForm.smul_slash, σ_SL, ← SlashAction.slash_mul, ← toGL_SL,
          ← toGL_mul (det_Mx_pos x).ne' (by simp)]
        exact key e g hg γ x
    _ = ∑ x, e (γ.val 1 1 : ZMod N) • (cx l e (σe x) • (g ∣[k] toGL (Mx l (σe x)))) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [smul_smul]; rfl
    _ = ∑ x, e (γ.val 1 1 : ZMod N) • (cx l e x • (g ∣[k] toGL (Mx l x))) :=
        Equiv.sum_comp σe (fun x => e (γ.val 1 1 : ZMod N) • (cx l e x • (g ∣[k] toGL (Mx l x))))

lemma isZeroAtImInfty_sum {ι : Type*} (s : Finset ι) (f : ι → ℍ → ℂ)
    (h : ∀ i ∈ s, IsZeroAtImInfty (f i)) : IsZeroAtImInfty (∑ i ∈ s, f i) := by
  unfold IsZeroAtImInfty Filter.ZeroAtFilter at *
  have := tendsto_finsetSum s h
  rw [Finset.sum_const_zero] at this
  convert this using 1
  funext b
  exact Finset.sum_apply b s f

/-- Rational matrices preserve the cusps of `Γ₁(N)`. -/
lemma isCusp_toGL_smul (hN : 0 < N) {c : OnePoint ℝ} (hc : IsCusp c (MTT.GammaOne N))
    (A : Matrix (Fin 2) (Fin 2) ℤ) : IsCusp (toGL A • c) (MTT.GammaOne N) := by
  have : NeZero N := ⟨hN.ne'⟩
  have h1 := hc.smul (toGL A)
  have h2 : (ConjAct.toConjAct (toGL A) • (MTT.GammaOne N)).IsArithmetic :=
    Subgroup.IsArithmetic.conj (MTT.GammaOne N) (toGLQ A)
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at h1 ⊢
  exact h1

/-- `T_l g` as a cusp form on `Γ₁(N)`. -/
def heckeCuspForm (hN : 0 < N) (e : DirichletCharacter ℂ N) {k : ℕ}
    (g : CuspForm (MTT.GammaOne N) (k : ℤ))
    (hg : ∀ γ' : Gamma0 N, (g : ℍ → ℂ) ∣[(k : ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ γ'.val =
      e (γ'.val 1 1 : ZMod N) • (g : ℍ → ℂ)) :
    CuspForm (MTT.GammaOne N) (k : ℤ) where
  toFun := T (l := l) e (k : ℤ) g
  slash_action_eq' := by
    rintro γ ⟨γ₀, hγ₀, rfl⟩
    have hγ₀' : γ₀ ∈ Gamma0 N := Gamma1_in_Gamma0 N hγ₀
    have h11 : ((γ₀ 1 1 : ℤ) : ZMod N) = 1 := ((Gamma1_mem N γ₀).mp hγ₀).2.1
    have := T_slash (l := l) e (g : ℍ → ℂ) hg ⟨γ₀, hγ₀'⟩
    rw [this]
    simp [h11]
  holo' := by
    unfold T
    exact MDifferentiable.sum fun x _ => ((ModularFormClass.holo g).slash _ _).const_smul _
  zero_at_cusps' := by
    intro c hc h hh
    unfold T
    rw [SlashAction.sum_slash]
    refine isZeroAtImInfty_sum _ _ fun x _ => ?_
    rw [ModularForm.smul_slash, ← SlashAction.slash_mul]
    apply Filter.ZeroAtFilter.smul
    have hc' : IsCusp (toGL (Mx l x) • c) (MTT.GammaOne N) := isCusp_toGL_smul hN hc _
    exact CuspFormClass.zero_at_cusps g hc' (toGL (Mx l x) * h) (by rw [mul_smul, hh])

end assemble

/-- **Hecke operators preserve cusp forms with nebentypus.** -/
theorem exists_cuspForm_heckePrime {N k : ℕ} (hN : 0 < N) (hk : 1 ≤ k)
    (e : DirichletCharacter ℂ N) (g : CuspForm (MTT.GammaOne N) (k : ℤ))
    (hg : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane,
      g ((Matrix.SpecialLinearGroup.mapGL ℝ γ.val) • z) =
        e (γ.val 1 1 : ZMod N) *
          (((γ.val 1 0 : ℤ) : ℂ) * z + ((γ.val 1 1 : ℤ) : ℂ)) ^ k * g z)
    (l : ℕ) (hl : l.Prime) :
    ∃ g' : CuspForm (MTT.GammaOne N) (k : ℤ),
      (∀ z, g' z = MTT.heckePrime k (e (l : ZMod N)) l g z) ∧
      ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane,
        g' ((Matrix.SpecialLinearGroup.mapGL ℝ γ.val) • z) =
          e (γ.val 1 1 : ZMod N) *
            (((γ.val 1 0 : ℤ) : ℂ) * z + ((γ.val 1 1 : ℤ) : ℂ)) ^ k * g' z := by
  have : Fact l.Prime := ⟨hl⟩
  have hg' : ∀ γ' : Gamma0 N, (g : ℍ → ℂ) ∣[(k : ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ γ'.val =
      e (γ'.val 1 1 : ZMod N) • (g : ℍ → ℂ) := slash_of_law e g hg
  refine ⟨heckeCuspForm (l := l) hN e g hg', fun z => ?_, fun γ z => ?_⟩
  · exact T_apply e hk g z
  · exact law_of_slash e _ γ (T_slash (l := l) e (g : ℍ → ℂ) hg' γ) z

end MTT.HeckePort

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 1 ≤ k) (e : DirichletCharacter ℂ N)
    (g : CuspForm (MTT.GammaOne N) (k : ℤ))
    (hg : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane,
      g ((Matrix.SpecialLinearGroup.mapGL ℝ γ.val) • z) =
        e (γ.val 1 1 : ZMod N) *
          (((γ.val 1 0 : ℤ) : ℂ) * z + ((γ.val 1 1 : ℤ) : ℂ)) ^ k * g z)
    (l : ℕ) (hl : l.Prime) :
    ∃ g' : CuspForm (MTT.GammaOne N) (k : ℤ),
      (∀ z, g' z = MTT.heckePrime k (e (l : ZMod N)) l g z) ∧
      ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ z : UpperHalfPlane,
        g' ((Matrix.SpecialLinearGroup.mapGL ℝ γ.val) • z) =
          e (γ.val 1 1 : ZMod N) *
            (((γ.val 1 0 : ℤ) : ℂ) * z + ((γ.val 1 1 : ℤ) : ℂ)) ^ k * g' z :=
  MTT.HeckePort.exists_cuspForm_heckePrime hN hk e g hg l hl
