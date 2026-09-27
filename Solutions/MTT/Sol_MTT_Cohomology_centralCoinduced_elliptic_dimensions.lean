import Definitions.MTT.Def_MTT_Cohomology
import Definitions.MTT.Def_MTT_FullParabolicCohomology
import Definitions.MTT.Def_MTT_ParabolicCohomology
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Trace
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Tactic

set_option autoImplicit false

/-! # Coinduction of a restricted representation as functions on left cosets -/

noncomputable section

namespace Rep

variable {K G : Type} [Field K] [Group G] (A : Rep K G) (H : Subgroup G)

def coindCosetCoordinates : coind H.subtype (res H.subtype A) ≃ₗ[K] (G ⧸ H → A) where
  toFun f := Quotient.lift (fun x : G => A.ρ x (f.val x⁻¹)) (by
    intro x y hxy
    have hh : x⁻¹ * y ∈ H := QuotientGroup.leftRel_apply.mp hxy
    let h : H := ⟨x⁻¹ * y, hh⟩
    have hy : y = x * h.val := by simp [h]
    rw [hy, mul_inv_rev]
    have hp := f.property h⁻¹ x⁻¹
    change f.val (h.val⁻¹ * x⁻¹) = A.ρ h.val⁻¹ (f.val x⁻¹) at hp
    rw [hp, ← Module.End.mul_apply, ← map_mul]
    simp only [mul_inv_cancel_right])
  invFun F := ⟨fun x => A.ρ x (F (QuotientGroup.mk x⁻¹)), by
    intro h x
    have hx : (QuotientGroup.mk ((h.val * x)⁻¹) : G ⧸ H) = QuotientGroup.mk x⁻¹ := by
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      simpa only [inv_inv, mul_inv_cancel_right] using h.property
    change A.ρ (h.val * x) (F (QuotientGroup.mk ((h.val * x)⁻¹))) =
      A.ρ h.val (A.ρ x (F (QuotientGroup.mk x⁻¹)))
    rw [hx, map_mul, Module.End.mul_apply]⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    change A.ρ x (A.ρ x⁻¹ (f.val x⁻¹⁻¹)) = f.val x
    rw [inv_inv, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  right_inv F := by
    funext q
    induction q using Quotient.inductionOn with
    | h x =>
        change A.ρ x (A.ρ x⁻¹ (F (QuotientGroup.mk x⁻¹⁻¹))) = F (QuotientGroup.mk x)
        rw [inv_inv, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
  map_add' f g := by
    funext q
    induction q using Quotient.inductionOn with
    | h x => exact map_add _ _ _
  map_smul' a f := by
    funext q
    induction q using Quotient.inductionOn with
    | h x => exact map_smul _ _ _

theorem coindCosetCoordinates_action (g : G) (f : coind H.subtype (res H.subtype A))
    (q : G ⧸ H) :
    coindCosetCoordinates A H ((coind H.subtype (res H.subtype A)).ρ g f) q =
      A.ρ g (coindCosetCoordinates A H f (g⁻¹ • q)) := by
  induction q using Quotient.inductionOn with
  | h x =>
      change A.ρ x (f.val (x⁻¹ * g)) = A.ρ g (A.ρ (g⁻¹ * x) (f.val (g⁻¹ * x)⁻¹))
      rw [mul_inv_rev, inv_inv, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

end Rep

/-! # Fixed-space dimensions from traces of cyclic averaging -/

noncomputable section

namespace LinearMap

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

def cyclicAverage (f : Module.End K V) (m : ℕ) : Module.End K V :=
  (m : K)⁻¹ • ∑ i ∈ Finset.range m, f ^ i

theorem isProj_cyclicAverage (f : Module.End K V) {m : ℕ} (hm : 0 < m)
    (hf : f ^ m = 1) : IsProj (f - 1).ker (cyclicAverage f m) where
  map_mem x := by
    rw [mem_ker]
    change ((f - 1) * cyclicAverage f m) x = 0
    rw [cyclicAverage, mul_smul_comm, mul_geom_sum, hf, sub_self, smul_zero, zero_apply]
  map_id x hx := by
    have hfx : f x = x := sub_eq_zero.mp hx
    have hi (i : ℕ) : (f ^ i) x = x := by
      induction i with
      | zero => rfl
      | succ i hi => rw [pow_succ', Module.End.mul_apply, hi, hfx]
    simp only [cyclicAverage, smul_apply, sum_apply, hi, Finset.sum_const,
      Finset.card_range, ← Nat.cast_smul_eq_nsmul K]
    rw [smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hm.ne'), one_smul]

theorem mul_finrank_ker_sub_one_eq_of_trace_powers
    [FiniteDimensional K V] (f : Module.End K V) {m : ℕ} (hm : 0 < m)
    (hf : f ^ m = 1)
    (ht : ∀ i ∈ Finset.Ico 1 m, trace K V (f ^ i) = 0) :
    m * Module.finrank K (f - 1).ker = Module.finrank K V := by
  have havg := (isProj_cyclicAverage f hm hf).trace
  have hs : ∑ i ∈ Finset.range m, trace K V (f ^ i) = Module.finrank K V := by
    rw [Finset.sum_eq_single 0]
    · simp only [pow_zero, trace_one]
    · intro i hi hi0
      exact ht i (Finset.mem_Ico.mpr ⟨by omega, Finset.mem_range.mp hi⟩)
    · simp [hm.ne']
  rw [cyclicAverage, map_smul, map_sum, hs, smul_eq_mul] at havg
  have he : (m : K) * Module.finrank K (f - 1).ker = Module.finrank K V := by
    rw [← havg, ← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hm.ne'), one_mul]
  exact_mod_cast he

end LinearMap

/-! # Vanishing traces for fixed-point-free coset actions -/

noncomputable section

namespace LinearMap

theorem trace_eq_zero_of_shift_without_fixed_points
    {K V X : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype X]
    (f : Module.End K (X → V)) (σ : X → X) (A : X → Module.End K V)
    (hf : ∀ v x, f v x = A x (v (σ x))) (hσ : ∀ x, σ x ≠ x) :
    trace K (X → V) f = 0 := by
  classical
  let b := Module.Free.chooseBasis K V
  rw [trace_eq_matrix_trace K (Pi.basis fun _ : X => b), Matrix.trace]
  apply Finset.sum_eq_zero
  intro i hi
  simp only [Matrix.diag_apply, toMatrix_apply, Pi.basis_repr, Pi.basis_apply, hf]
  rw [Pi.single_eq_of_ne (hσ i.1), map_zero, map_zero, Finsupp.zero_apply]

end LinearMap

namespace Rep

theorem trace_coind_eq_zero_of_coset_without_fixed_points
    {K G : Type} [Field K] [Group G] (A : Rep K G) (H : Subgroup G)
    [FiniteDimensional K A] [Finite (G ⧸ H)] (g : G)
    (hg : ∀ q : G ⧸ H, g • q ≠ q) :
    LinearMap.trace K (coind H.subtype (res H.subtype A))
      ((coind H.subtype (res H.subtype A)).ρ g) = 0 := by
  classical
  let := Fintype.ofFinite (G ⧸ H)
  let e := coindCosetCoordinates A H
  rw [← LinearMap.trace_conj' _ e]
  apply LinearMap.trace_eq_zero_of_shift_without_fixed_points
    (σ := fun q => g⁻¹ • q) (A := fun _ => A.ρ g)
  · intro v q
    change e ((coind H.subtype (res H.subtype A)).ρ g (e.symm v)) q = _
    rw [coindCosetCoordinates_action, e.apply_symm_apply]
  · intro q hq
    apply hg q
    simpa only [smul_inv_smul] using (congrArg (fun x => g • x) hq).symm

end Rep

/-! # The global symmetric-power representation underlying the MTT coefficients -/

noncomputable section

open scoped MatrixGroups

namespace MTT.Cohomology

def fullSymRep (n : ℕ) : Rep ℂ SL(2, ℤ) :=
  Rep.of ((symRepresentation ⊤ n ℂ).ρ.comp
    { toFun := fun g => ⟨g, Subgroup.mem_top g⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl })

theorem gammaOneRep_eq_res_fullSymRep (N n : ℕ) :
    gammaOneRep N n = Rep.res (CongruenceSubgroup.Gamma1 N).subtype (fullSymRep n) := rfl

end MTT.Cohomology

/-! # Trace obstructions to elliptic fixed cosets at large Gamma1 level -/

open scoped MatrixGroups

namespace MTT.Cohomology

theorem trace_conjugate_SL (g x : SL(2, ℤ)) :
    Matrix.trace (x⁻¹ * g * x).val = Matrix.trace g.val := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.trace_mul_cycle, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]

theorem gammaOne_dvd_two_sub_trace {N : ℕ} {g : SL(2, ℤ)}
    (hg : g ∈ CongruenceSubgroup.Gamma1 N) : (N : ℤ) ∣ 2 - Matrix.trace g.val := by
  obtain ⟨ha, hd, _⟩ := (CongruenceSubgroup.Gamma1_mem N g).mp hg
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Int.cast_sub, Int.cast_add,
    Int.cast_ofNat]
  change (2 : ZMod N) - ((g 0 0 : ZMod N) + (g 1 1 : ZMod N)) = 0
  rw [ha, hd]
  ring

theorem gammaOne_coset_smul_ne_of_trace {N : ℕ} (hN : 5 ≤ N) {g : SL(2, ℤ)}
    (ht₁ : -2 ≤ Matrix.trace g.val) (ht₂ : Matrix.trace g.val < 2)
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N) : g • q ≠ q := by
  induction q using Quotient.inductionOn with
  | h x =>
      intro hq
      have hx : x⁻¹ * g * x ∈ CongruenceSubgroup.Gamma1 N := by
        have hx := Quotient.exact hq.symm
        simpa only [QuotientGroup.leftRel_apply, smul_eq_mul, mul_assoc] using hx
      have hd := gammaOne_dvd_two_sub_trace hx
      rw [trace_conjugate_SL] at hd
      have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega :
        0 ≤ 2 - Matrix.trace g.val) (by omega : 2 - Matrix.trace g.val < (N : ℤ)) hd
      omega

theorem S_pow_two : ModularGroup.S ^ 2 = (-1 : SL(2, ℤ)) := by decide

theorem ST_pow_three : (ModularGroup.S * ModularGroup.T) ^ 3 = (-1 : SL(2, ℤ)) := by
  decide

theorem neg_one_pow_two : (-1 : SL(2, ℤ)) ^ 2 = 1 := by decide

theorem S_pow_four : ModularGroup.S ^ 4 = (1 : SL(2, ℤ)) := by
  rw [show 4 = 2 * 2 from rfl, pow_mul, S_pow_two, neg_one_pow_two]

theorem ST_pow_six : (ModularGroup.S * ModularGroup.T) ^ 6 = (1 : SL(2, ℤ)) := by
  rw [show 6 = 3 * 2 from rfl, pow_mul, ST_pow_three, neg_one_pow_two]

theorem gammaOne_coset_neg_one_ne {N : ℕ} (hN : 5 ≤ N)
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N) : (-1 : SL(2, ℤ)) • q ≠ q :=
  gammaOne_coset_smul_ne_of_trace hN (by decide) (by decide) q

theorem gammaOne_coset_S_pow_ne {N : ℕ} (hN : 5 ≤ N) {i : ℕ}
    (hi : i ∈ Finset.Ico 1 4) (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N) :
    ModularGroup.S ^ i • q ≠ q := by
  apply gammaOne_coset_smul_ne_of_trace hN
  all_goals
    have hi₁ := (Finset.mem_Ico.mp hi).1
    have hi₂ := (Finset.mem_Ico.mp hi).2
    interval_cases i <;> decide

theorem gammaOne_coset_ST_pow_ne {N : ℕ} (hN : 5 ≤ N) {i : ℕ}
    (hi : i ∈ Finset.Ico 1 6) (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N) :
    (ModularGroup.S * ModularGroup.T) ^ i • q ≠ q := by
  apply gammaOne_coset_smul_ne_of_trace hN
  all_goals
    have hi₁ := (Finset.mem_Ico.mp hi).1
    have hi₂ := (Finset.mem_Ico.mp hi).2
    interval_cases i <;> decide

end MTT.Cohomology

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


end MTT.Cohomology

/-! # Finite-order fixed dimensions in the full coinduced coefficient module -/

noncomputable section

open scoped MatrixGroups

namespace MTT.Cohomology

abbrev fullCoinduced (N n : ℕ) :=
  Rep.coind (CongruenceSubgroup.Gamma1 N).subtype (gammaOneRep N n)

def fullCoinducedCoordinates (N n : ℕ) :
    fullCoinduced N n ≃ₗ[ℂ] (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N → fullSymRep n) :=
  Rep.coindCosetCoordinates (fullSymRep n) (CongruenceSubgroup.Gamma1 N)

instance fullSymRep_finiteDimensional (n : ℕ) : FiniteDimensional ℂ (fullSymRep n) :=
  Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 2) ℂ n)

instance fullCoinduced_finiteDimensional (N n : ℕ) [NeZero N] :
    FiniteDimensional ℂ (fullCoinduced N n) :=
  FiniteDimensional.of_injective (fullCoinducedCoordinates N n).toLinearMap
    (fullCoinducedCoordinates N n).injective

theorem finrank_fullCoinduced (N n : ℕ) [NeZero N] :
    Module.finrank ℂ (fullCoinduced N n) = (CongruenceSubgroup.Gamma1 N).index * (n + 1) := by
  classical
  let := Fintype.ofFinite (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N)
  rw [(fullCoinducedCoordinates N n).finrank_eq, Module.finrank_pi_fintype]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change Fintype.card (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N) *
    Module.finrank ℂ (Sym ℂ n) = _
  rw [finrank_sym, Fintype.card_eq_nat_card]
  rfl

theorem trace_fullCoinduced_eq_zero {N n : ℕ} [NeZero N] (g : SL(2, ℤ))
    (hg : ∀ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma1 N, g • q ≠ q) :
    LinearMap.trace ℂ (fullCoinduced N n) ((fullCoinduced N n).ρ g) = 0 :=
  Rep.trace_coind_eq_zero_of_coset_without_fixed_points (fullSymRep n)
    (CongruenceSubgroup.Gamma1 N) g hg

theorem fullCoinduced_fixed_neg_one_finrank {N n : ℕ} (hN : 5 ≤ N) :
    2 * Module.finrank ℂ ((fullCoinduced N n).ρ (-1) - 1).ker =
      Module.finrank ℂ (fullCoinduced N n) := by
  have : NeZero N := ⟨by omega⟩
  apply LinearMap.mul_finrank_ker_sub_one_eq_of_trace_powers _ (by decide)
  · rw [← map_pow, neg_one_pow_two, map_one]
  · intro i hi
    have hi : i = 1 := by simp only [Finset.mem_Ico] at hi; omega
    subst i
    rw [pow_one]
    exact trace_fullCoinduced_eq_zero _ (gammaOne_coset_neg_one_ne hN)

theorem fullCoinduced_fixed_S_finrank {N n : ℕ} (hN : 5 ≤ N) :
    4 * Module.finrank ℂ ((fullCoinduced N n).ρ ModularGroup.S - 1).ker =
      Module.finrank ℂ (fullCoinduced N n) := by
  have : NeZero N := ⟨by omega⟩
  apply LinearMap.mul_finrank_ker_sub_one_eq_of_trace_powers _ (by decide)
  · rw [← map_pow, S_pow_four, map_one]
  · intro i hi
    rw [← map_pow]
    exact trace_fullCoinduced_eq_zero _ (gammaOne_coset_S_pow_ne hN hi)

theorem fullCoinduced_fixed_ST_finrank {N n : ℕ} (hN : 5 ≤ N) :
    6 * Module.finrank ℂ
        ((fullCoinduced N n).ρ (ModularGroup.S * ModularGroup.T) - 1).ker =
      Module.finrank ℂ (fullCoinduced N n) := by
  have : NeZero N := ⟨by omega⟩
  apply LinearMap.mul_finrank_ker_sub_one_eq_of_trace_powers _ (by decide)
  · rw [← map_pow, ST_pow_six, map_one]
  · intro i hi
    rw [← map_pow]
    exact trace_fullCoinduced_eq_zero _ (gammaOne_coset_ST_pow_ne hN hi)

end MTT.Cohomology

/-! # Generator-fixed vectors are fixed by a central power -/

noncomputable section

namespace Rep

variable {G : Type} [Group G] (A : Rep ℂ G) (z : G) (hz : ∀ g, z * g = g * z)

def centralFixedGeneratorEquiv (g : G) {m : ℕ} (hgm : g ^ m = z) :
    ((centralFixedRep A z hz).ρ g - 1).ker ≃ₗ[ℂ] (A.ρ g - 1).ker where
  toFun v := ⟨v.val.val, by
    have hv : (centralFixedRep A z hz).ρ g v.val = v.val := sub_eq_zero.mp v.property
    exact sub_eq_zero.mpr (congrArg Subtype.val hv)⟩
  invFun v := ⟨⟨v.val, by
    rw [mem_centralFixed, ← hgm, map_pow]
    have hv : A.ρ g v.val = v.val := sub_eq_zero.mp v.property
    clear hgm
    induction m with
    | zero => rfl
    | succ m hm => rw [pow_succ', Module.End.mul_apply, hm, hv]⟩, by
      apply sub_eq_zero.mpr
      exact Subtype.ext (sub_eq_zero.mp v.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Rep

/-! # The index change on adjoining the central involution -/

open scoped MatrixGroups

namespace MTT.Cohomology

theorem mem_sup_neg_one_iff (H : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) :
    g ∈ H ⊔ Subgroup.zpowers (-1) ↔ g ∈ H ∨ -g ∈ H := by
  let K : Subgroup SL(2, ℤ) :=
    { carrier := {g | g ∈ H ∨ -g ∈ H}
      one_mem' := Or.inl H.one_mem
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (H.mul_mem ha hb)
        · exact Or.inr (by simpa using H.mul_mem ha hb)
        · exact Or.inr (by simpa using H.mul_mem ha hb)
        · exact Or.inl (by simpa using H.mul_mem ha hb)
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (H.inv_mem ha)
        · exact Or.inr (by simpa using H.inv_mem ha) }
  have hle : H ⊔ Subgroup.zpowers (-1) ≤ K := by
    refine sup_le (fun _ h => Or.inl h) (Subgroup.zpowers_le.mpr ?_)
    exact Or.inr (by simpa only [neg_neg] using H.one_mem)
  refine ⟨fun h => hle h, ?_⟩
  rintro (h | h)
  · exact Subgroup.mem_sup_left h
  · have hm := Subgroup.mul_mem_sup h (Subgroup.mem_zpowers (-1 : SL(2, ℤ)))
    simpa using hm

theorem gammaOne_neg_one_not_mem {N : ℕ} (hN : 5 ≤ N) :
    (-1 : SL(2, ℤ)) ∉ CongruenceSubgroup.Gamma1 N := by
  intro h
  have hd := gammaOne_dvd_two_sub_trace h
  have ht : Matrix.trace (-1 : SL(2, ℤ)).val = -2 := by decide
  rw [ht] at hd
  have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt (by norm_num : (0 : ℤ) ≤ 2 - -2)
    (by omega : (2 : ℤ) - -2 < N) hd
  norm_num at hz

theorem gammaOne_central_index {N : ℕ} (hN : 5 ≤ N) :
    2 * (CongruenceSubgroup.Gamma1 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index =
      (CongruenceSubgroup.Gamma1 N).index := by
  have hr : (CongruenceSubgroup.Gamma1 N).relIndex
      (CongruenceSubgroup.Gamma1 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) = 2 := by
    apply Subgroup.relIndex_eq_two_iff_exists_notMem_and.mpr
    refine ⟨-1, Subgroup.mem_sup_right (Subgroup.mem_zpowers _),
      gammaOne_neg_one_not_mem hN, ?_⟩
    intro b hb
    rcases (mem_sup_neg_one_iff _ b).mp hb with hb | hb
    · exact Or.inr hb
    · exact Or.inl (by simpa using hb)
  have hi := Subgroup.relIndex_mul_index (show CongruenceSubgroup.Gamma1 N ≤
    CongruenceSubgroup.Gamma1 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) from le_sup_left)
  rwa [hr] at hi

end MTT.Cohomology

/-! # Central coefficient dimension and elliptic fixed spaces -/

noncomputable section

open scoped MatrixGroups

namespace MTT.Cohomology

theorem solution {N n : ℕ} (hN : 5 ≤ N) :
    Module.finrank ℂ (centralCoinduced N n) =
        (n + 1) * (CongruenceSubgroup.Gamma1 N ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ∧
      2 * Module.finrank ℂ ((centralCoinduced N n).ρ ModularGroup.S - LinearMap.id).ker =
        Module.finrank ℂ (centralCoinduced N n) ∧
      3 * Module.finrank ℂ
        ((centralCoinduced N n).ρ (ModularGroup.S * ModularGroup.T) - LinearMap.id).ker =
        Module.finrank ℂ (centralCoinduced N n) := by
  have : NeZero N := ⟨by omega⟩
  have hd := fullCoinduced_fixed_neg_one_finrank (n := n) hN
  change 2 * Module.finrank ℂ (centralCoinduced N n) =
    Module.finrank ℂ (fullCoinduced N n) at hd
  refine ⟨?_, ?_, ?_⟩
  · rw [finrank_fullCoinduced, ← gammaOne_central_index hN] at hd
    nlinarith [hd]
  · have hS := fullCoinduced_fixed_S_finrank (n := n) hN
    have he := (Rep.centralFixedGeneratorEquiv (fullCoinduced N n) (-1)
      neg_one_central ModularGroup.S S_pow_two).finrank_eq
    change Module.finrank ℂ
        ((centralCoinduced N n).ρ ModularGroup.S - LinearMap.id).ker = _ at he
    rw [← he] at hS
    omega
  · have hU := fullCoinduced_fixed_ST_finrank (n := n) hN
    have he := (Rep.centralFixedGeneratorEquiv (fullCoinduced N n) (-1)
      neg_one_central (ModularGroup.S * ModularGroup.T) ST_pow_three).finrank_eq
    change Module.finrank ℂ
        ((centralCoinduced N n).ρ (ModularGroup.S * ModularGroup.T) - LinearMap.id).ker = _ at he
    rw [← he] at hU
    omega

end MTT.Cohomology

export MTT.Cohomology (solution)
