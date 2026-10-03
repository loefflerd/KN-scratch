module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

import Mathlib.RingTheory.SimpleRing.Principal

section privateSection

namespace WeierstrassCurve

open WeierstrassCurve

variable {R : Type*} [CommRing R]

theorem negVariableChange_smul (W : WeierstrassCurve R) :
    (⟨-1, 0, -W.a₁, -W.a₃⟩ : VariableChange R) • W = W := by
  ext
  · simp only [variableChange_a₁, inv_neg, inv_one, Units.val_neg, Units.val_one]; ring
  · simp only [variableChange_a₂, inv_neg, inv_one, Units.val_neg, Units.val_one]; ring
  · simp only [variableChange_a₃, inv_neg, inv_one, Units.val_neg, Units.val_one]; ring
  · simp only [variableChange_a₄, inv_neg, inv_one, Units.val_neg, Units.val_one]; ring
  · simp only [variableChange_a₆, inv_neg, inv_one, Units.val_neg, Units.val_one]; ring

end WeierstrassCurve

open WeierstrassCurve

theorem solution {F : Type*} [Field F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (E : WeierstrassCurve F)
    (hc₄ : E.c₄ ≠ 0) (hc₆ : E.c₆ ≠ 0) (C : VariableChange F) :
    C • E = E ↔ C = 1 ∨ C = ⟨-1, 0, -E.a₁, -E.a₃⟩ := by
  constructor
  · intro h
    obtain ⟨u, r, s, t⟩ := C

    have h4 : ((u : F)⁻¹) ^ 4 = 1 := by
      have := congrArg WeierstrassCurve.c₄ h
      rw [variableChange_c₄, Units.val_inv_eq_inv_val] at this
      exact (mul_eq_right₀ hc₄).mp this
    have h6 : ((u : F)⁻¹) ^ 6 = 1 := by
      have := congrArg WeierstrassCurve.c₆ h
      rw [variableChange_c₆, Units.val_inv_eq_inv_val] at this
      exact (mul_eq_right₀ hc₆).mp this
    have hsq : (u : F)⁻¹ * (u : F)⁻¹ = 1 := by
      have : ((u : F)⁻¹) ^ 6 = ((u : F)⁻¹) ^ 4 * (((u : F)⁻¹) * ((u : F)⁻¹)) := by ring
      rw [this, h4, one_mul] at h6
      exact h6
    have huinv : (u : F)⁻¹ = 1 ∨ (u : F)⁻¹ = -1 := mul_self_eq_one_iff.mp hsq
    have h1 := congrArg WeierstrassCurve.a₁ h
    have h2' := congrArg WeierstrassCurve.a₂ h
    have h3' := congrArg WeierstrassCurve.a₃ h
    simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃,
      Units.val_inv_eq_inv_val] at h1 h2' h3'
    rcases huinv with hui | hui
    · left
      have hu : (u : F) = 1 := by rw [← inv_inv (u : F), hui, inv_one]
      rw [hui] at h1 h2' h3'
      have hs : s = 0 := by
        have : (2 : F) * s = 0 := by linear_combination h1
        exact (mul_eq_zero.mp this).resolve_left h2
      subst hs
      have hr : r = 0 := by
        have : (3 : F) * r = 0 := by linear_combination h2'
        exact (mul_eq_zero.mp this).resolve_left h3
      subst hr
      have ht : t = 0 := by
        have : (2 : F) * t = 0 := by linear_combination h3'
        exact (mul_eq_zero.mp this).resolve_left h2
      subst ht
      have huu : u = 1 := Units.ext hu
      subst huu
      rfl
    · right
      have hu : (u : F) = -1 := by rw [← inv_inv (u : F), hui, inv_neg, inv_one]
      rw [hui] at h1 h2' h3'
      have hs : s = -E.a₁ := by
        have : (2 : F) * (s + E.a₁) = 0 := by linear_combination -h1
        linear_combination (mul_eq_zero.mp this).resolve_left h2
      subst hs
      have hr : r = 0 := by
        have : (3 : F) * r = 0 := by linear_combination h2'
        exact (mul_eq_zero.mp this).resolve_left h3
      subst hr
      have ht : t = -E.a₃ := by
        have : (2 : F) * (t + E.a₃) = 0 := by linear_combination -h3'
        linear_combination (mul_eq_zero.mp this).resolve_left h2
      subst ht
      have huu : u = -1 := Units.ext (by rw [hu, Units.val_neg, Units.val_one])
      subst huu
      rfl
  · rintro (rfl | rfl)
    · exact one_smul _ _
    · exact negVariableChange_smul E

end privateSection

public section publicSection

theorem WeierstrassCurve.variableChange_smul_eq_self_iff_of_c4_ne_zero_of_c6_ne_zero
    {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (E : WeierstrassCurve F)
    (hc₄ : E.c₄ ≠ 0) (hc₆ : E.c₆ ≠ 0) (C : WeierstrassCurve.VariableChange F) :
    C • E = E ↔ C = 1 ∨ C = ⟨-1, 0, -E.a₁, -E.a₃⟩ := by
  exact solution h2 h3 E hc₄ hc₆ C

end publicSection
