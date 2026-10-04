import Definitions.MTT.Def_MTT_Cohomology
import Theorems.MTT.Thm_MTT_Cohomology_integration_map
import Theorems.MTT.Thm_MTT_Cohomology_packet_span
import Theorems.MTT.Thm_MTT_Cohomology_reflection_involutive
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

namespace P2MSPMO

variable {R : Type*} [CommRing R]

/-- The reflection is additive and homogeneous in the cochain. -/
theorem reflection_add_smul (a b : R) (φ ψ : (Cusp × Cusp) → Binary R) :
    reflection (a • φ + b • ψ) = a • reflection φ + b • reflection ψ := by
  funext D
  simp [reflection]

theorem reflection_smul (a : R) (φ : (Cusp × Cusp) → Binary R) :
    reflection (a • φ) = a • reflection φ := by
  funext D
  simp [reflection]

/-- Pure linear algebra: two vectors in the span of `x` and `y = r x` that are both
`s`-eigenvectors of an involution `r` swapping `x` and `y` are linearly dependent. -/
theorem dependent_of_span {M : Type*} [AddCommGroup M] [Module ℂ M]
    (r : M → M) (hr_smul : ∀ (a b : ℂ) (u v : M), r (a • u + b • v) = a • r u + b • r v)
    (x : M) (hrr : r (r x) = x) (σ : ℂ)
    (φ ψ : M) (hφ : r φ = σ • φ) (hψ : r ψ = σ • ψ)
    (c d : ℂ) (hcd : φ = c • x + d • r x)
    (c' d' : ℂ) (hcd' : ψ = c' • x + d' • r x) :
    ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ a • φ + b • ψ = 0 := by
  -- the eigen-relations, spelled out on the coordinates
  have key : ∀ (c d : ℂ) (φ : M), φ = c • x + d • r x → r φ = σ • φ →
      (d - σ * c) • x + (c - σ * d) • r x = 0 := by
    intro c d φ h hφ
    have h1 : r φ = c • r x + d • x := by rw [h, hr_smul, hrr]
    have h2 : r φ = (σ * c) • x + (σ * d) • r x := by rw [hφ, h, smul_add, smul_smul, smul_smul]
    have h3 : c • r x + d • x = (σ * c) • x + (σ * d) • r x := h1.symm.trans h2
    have : (d - σ * c) • x + (c - σ * d) • r x =
        (c • r x + d • x) - ((σ * c) • x + (σ * d) • r x) := by
      simp only [sub_smul]; abel
    rw [this, h3, sub_self]
  by_cases hx : x = 0
  · -- everything is a multiple of `r x`
    subst hx
    have h0 : r (0 : M) = 0 := by simpa using hr_smul 0 0 0 0
    have hφ0 : φ = 0 := by rw [hcd, h0]; simp
    exact ⟨1, 0, Or.inl one_ne_zero, by simp [hφ0]⟩
  by_cases hdep : ∃ l : ℂ, r x = l • x
  · obtain ⟨l, hl⟩ := hdep
    have hφ' : φ = (c + d * l) • x := by rw [hcd, hl, smul_smul, add_smul]
    have hψ' : ψ = (c' + d' * l) • x := by rw [hcd', hl, smul_smul, add_smul]
    by_cases hz : c + d * l = 0
    · refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩
      rw [hφ', hz]; simp
    · refine ⟨c' + d' * l, -(c + d * l), Or.inr (neg_ne_zero.mpr hz), ?_⟩
      rw [hφ', hψ', smul_smul, smul_smul, mul_comm (c' + d' * l), neg_mul, neg_smul,
        add_neg_cancel]
  · -- `x` and `r x` are independent: the coefficients are forced
    push Not at hdep
    have indep : ∀ a b : ℂ, a • x + b • r x = 0 → a = 0 ∧ b = 0 := by
      intro a b hab
      by_cases hb : b = 0
      · subst hb
        simp only [zero_smul, add_zero, smul_eq_zero] at hab
        exact ⟨hab.resolve_right hx, rfl⟩
      · exfalso
        apply hdep (-(a / b))
        have h1 : b • r x = -(a • x) := by
          rw [eq_neg_iff_add_eq_zero, add_comm]; exact hab
        calc r x = b⁻¹ • (b • r x) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
          _ = -(a / b) • x := by rw [h1, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
    have hφc := indep _ _ (key c d φ hcd hφ)
    have hψc := indep _ _ (key c' d' ψ hcd' hψ)
    have hd : d = σ * c := sub_eq_zero.mp hφc.1
    have hd' : d' = σ * c' := sub_eq_zero.mp hψc.1
    have hφ' : φ = c • (x + σ • r x) := by rw [hcd, hd, smul_add, smul_smul, mul_comm c σ]
    have hψ' : ψ = c' • (x + σ • r x) := by rw [hcd', hd', smul_add, smul_smul, mul_comm c' σ]
    by_cases hz : c = 0
    · refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩
      rw [hφ', hz]; simp
    · refine ⟨c', -c, Or.inr (neg_ne_zero.mpr hz), ?_⟩
      rw [hφ', hψ', smul_smul, smul_smul, mul_comm c', neg_mul, neg_smul, add_neg_cancel]

end P2MSPMO

open P2MSPMO in
theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (s : Bool) (φ ψ : Hc N (k-2) ℂ)
    (hφ : Packet (fun d => ι (f.epsilon d)) (fun l => ι (f.coeff l)) s φ)
    (hψ : Packet (fun d => ι (f.epsilon d)) (fun l => ι (f.coeff l)) s ψ) :
    ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ a • φ + b • ψ = 0 := by
  obtain ⟨I, -, hT, hI⟩ := MTT.Cohomology.integration_map hN hk
  obtain ⟨c, d, hcd⟩ :=
    MTT.Cohomology.packet_span hN hk I hI hT ι f φ hφ.1 hφ.2.1
  obtain ⟨c', d', hcd'⟩ :=
    MTT.Cohomology.packet_span hN hk I hI hT ι f ψ hψ.1 hψ.2.1
  obtain ⟨a, b, hab, h⟩ := dependent_of_span (M := (Cusp × Cusp) → Binary ℂ) reflection
    (fun a b u v => reflection_add_smul a b u v) (I f.form).val
    (MTT.Cohomology.reflection_involutive _) (MTT.sign s : ℂ)
    φ.val ψ.val hφ.2.2 hψ.2.2 c d hcd c' d' hcd'
  exact ⟨a, b, hab, Subtype.ext (by simpa using h)⟩
