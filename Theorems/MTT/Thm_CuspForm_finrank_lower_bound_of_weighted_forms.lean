module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.LinearAlgebra.Dimension.Finite

import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-! # Independent power series from successive vanishing orders -/

open UpperHalfPlane
open scoped MatrixGroups

noncomputable section privateSection

namespace PowerSeries

variable {K : Type*} [Field K]

theorem linearIndependent_of_order_eq {m : ℕ} (v : Fin m → PowerSeries K)
    (hv : ∀ i, (v i).order = i.val) : LinearIndependent K v := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha
  have hall : ∀ n : ℕ, ∀ i : Fin m, i.val = n → a i = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hi
      have hc := congrArg (coeff i.val) ha
      simp only [map_sum, coeff_smul, smul_eq_mul, map_zero] at hc
      have hs : (∑ j : Fin m, a j * coeff i.val (v j)) = a i * coeff i.val (v i) := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          rcases lt_or_gt_of_ne hji with hj | hj
          · rw [ih j.val (by omega) j rfl, zero_mul]
          · rw [coeff_of_lt_order _ (by rw [hv]; exact_mod_cast hj), mul_zero]
        · simp
      rw [hs] at hc
      exact (mul_eq_zero.mp hc).resolve_right ((order_eq_nat.mp (hv i)).1)
  exact fun i => hall i.val i rfl

theorem linearIndependent_weighted_powers (A B : PowerSeries K)
    (hA : A.order = 0) (hB : B.order = 1) {m : ℕ} (e : Fin m → ℕ) :
    LinearIndependent K (fun i : Fin m => A ^ e i * B ^ i.val) := by
  apply linearIndependent_of_order_eq
  intro i
  simp only [order_mul, order_pow, hA, hB, smul_zero, zero_add, nsmul_one]

theorem linearIndependent_mul_weighted_powers (A B D : PowerSeries K)
    (hA : A.order = 0) (hB : B.order = 1) (hD : D ≠ 0)
    {m : ℕ} (e : Fin m → ℕ) :
    LinearIndependent K (fun i : Fin m => D * (A ^ e i * B ^ i.val)) := by
  let f : PowerSeries K →ₗ[K] PowerSeries K :=
    { toFun := fun P => D * P
      map_add' := mul_add D
      map_smul' := fun a P => by simp only [RingHom.id_apply, mul_smul_comm] }
  have hf : Function.Injective f := by
    intro P Q h
    exact mul_left_cancel₀ hD h
  exact (linearIndependent_weighted_powers A B hA hB e).map' f
    (LinearMap.ker_eq_bot.mpr hf)

end PowerSeries

/-! # Cusp-form families from two weighted modular forms -/

section DL_stomaching

namespace CuspForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]

def qExpansionLinear (h : ℝ) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (k : ℤ) :
    CuspForm Γ k →ₗ[ℂ] PowerSeries ℂ where
  toFun f := qExpansion h f
  map_add' f g := ModularForm.qExpansion_add hh hΓ f g
  map_smul' a f := ModularForm.qExpansion_smul hh hΓ a f

def weightedFamily {d r k : ℕ} (_hd : 0 < d) (hr : r ≤ k)
    (A : ModularForm Γ 1) (B : ModularForm Γ (d : ℤ)) (D : CuspForm Γ (r : ℤ))
    (i : Fin ((k - r) / d + 1)) : CuspForm Γ (k : ℤ) :=
  (D.mulModularForm ((A.pow (k - r - d * i.val)).mul (B.pow i.val))).mcast (by
    have hi : d * i.val ≤ k - r := by
      have h := Nat.mul_le_mul_left d (show i.val ≤ (k - r) / d by omega)
      exact h.trans (by simpa [Nat.mul_comm] using Nat.div_mul_le_self (k - r) d)
    rw [mul_comm (i.val : ℤ) (d : ℤ)]
    omega)

theorem qExpansion_weightedFamily {d r k : ℕ} (hd : 0 < d) (hr : r ≤ k)
    (A : ModularForm Γ 1) (B : ModularForm Γ (d : ℤ)) (D : CuspForm Γ (r : ℤ))
    (h : ℝ) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (i : Fin ((k - r) / d + 1)) :
    qExpansion h (weightedFamily hd hr A B D i) =
      qExpansion h D * ((qExpansion h A) ^ (k - r - d * i.val) *
        (qExpansion h B) ^ i.val) := by
  change qExpansion h (D.mulModularForm
    ((A.pow (k - r - d * i.val)).mul (B.pow i.val))) = _
  rw [show qExpansion h (D.mulModularForm
      ((A.pow (k - r - d * i.val)).mul (B.pow i.val))) =
      qExpansion h D * qExpansion h ((A.pow (k - r - d * i.val)).mul (B.pow i.val)) from
        ModularForm.qExpansion_mul_coe hh hΓ D
          ((A.pow (k - r - d * i.val)).mul (B.pow i.val)),
    ModularForm.qExpansion_mul hh hΓ, ModularForm.qExpansion_pow hh hΓ,
    ModularForm.qExpansion_pow hh hΓ]

theorem weightedFamily_linearIndependent {d r k : ℕ} (hd : 0 < d) (hr : r ≤ k)
    (A : ModularForm Γ 1) (B : ModularForm Γ (d : ℤ)) (D : CuspForm Γ (r : ℤ))
    (h : ℝ) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (hA : (qExpansion h A).order = 0) (hB : (qExpansion h B).order = 1) (hD : D ≠ 0) :
    LinearIndependent ℂ (weightedFamily hd hr A B D) := by
  have hDq : qExpansion h D ≠ 0 := by
    have hD' : (D : ModularForm Γ (r : ℤ)) ≠ 0 := by
      intro hz
      apply hD
      exact DFunLike.ext _ _ (fun z =>
        congrArg (fun f : ModularForm Γ (r : ℤ) => f z) hz)
    exact (ModularForm.qExpansion_eq_zero_iff hh hΓ
      (D : ModularForm Γ (r : ℤ))).not.mpr hD'
  apply LinearIndependent.of_comp (qExpansionLinear h hh hΓ (k : ℤ))
  have hi := PowerSeries.linearIndependent_mul_weighted_powers
    (qExpansion h A) (qExpansion h B) (qExpansion h D) hA hB hDq
    (fun i : Fin ((k - r) / d + 1) => k - r - d * i.val)
  change LinearIndependent ℂ (fun i => qExpansion h (weightedFamily hd hr A B D i))
  have heq : (fun i => qExpansion h (weightedFamily hd hr A B D i)) =
      (fun i : Fin ((k - r) / d + 1) =>
        qExpansion h D * ((qExpansion h A) ^ (k - r - d * i.val) *
          (qExpansion h B) ^ i.val)) :=
    funext (qExpansion_weightedFamily hd hr A B D h hh hΓ)
  rw [heq]
  exact hi

theorem finrank_lower_bound_of_weighted_forms_aux {d r k : ℕ} (hd : 0 < d) (hr : r ≤ k)
    (A : ModularForm Γ 1) (B : ModularForm Γ (d : ℤ)) (D : CuspForm Γ (r : ℤ))
    (h : ℝ) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (hA : (qExpansion h A).order = 0) (hB : (qExpansion h B).order = 1) (hD : D ≠ 0)
    [FiniteDimensional ℂ (CuspForm Γ (k : ℤ))] :
    (k - r) / d + 1 ≤ Module.finrank ℂ (CuspForm Γ (k : ℤ)) := by
  simpa only [Fintype.card_fin] using
    (weightedFamily_linearIndependent hd hr A B D h hh hΓ hA hB hD).fintype_card_le_finrank

end CuspForm

theorem solution {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]
    {d r k : ℕ} (hd : 0 < d) (hr : r ≤ k)
    (A : ModularForm Γ 1) (B : ModularForm Γ (d : ℤ)) (D : CuspForm Γ (r : ℤ))
    (h : ℝ) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (hA : MvPowerSeries.order (qExpansion h A) = 0)
    (hB : MvPowerSeries.order (qExpansion h B) = 1) (hD : D ≠ 0)
    [FiniteDimensional ℂ (CuspForm Γ (k : ℤ))] :
    (k - r) / d + 1 ≤ Module.finrank ℂ (CuspForm Γ (k : ℤ)) :=
  CuspForm.finrank_lower_bound_of_weighted_forms_aux hd hr A B D h hh hΓ
    (PowerSeries.order_eq_order.trans hA) (PowerSeries.order_eq_order.trans hB) hD

end DL_stomaching

end privateSection

public section publicSection

theorem CuspForm.finrank_lower_bound_of_weighted_forms
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] {d r k : ℕ} (hd : 0 < d) (hr : r ≤ k)
    (A : ModularForm Γ 1) (B : ModularForm Γ (d : ℤ)) (D : CuspForm Γ (r : ℤ))
    (h : ℝ) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (hA : (qExpansion h A).order = 0) (hB : (qExpansion h B).order = 1) (hD : D ≠ 0)
    [FiniteDimensional ℂ (CuspForm Γ (k : ℤ))] :
    (k - r) / d + 1 ≤ Module.finrank ℂ (CuspForm Γ (k : ℤ)) :=
  solution hd hr A B D h hh hΓ hA hB hD

end publicSection
