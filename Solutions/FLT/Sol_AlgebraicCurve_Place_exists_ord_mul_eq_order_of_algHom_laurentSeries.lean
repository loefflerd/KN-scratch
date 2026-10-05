import Mathlib.RingTheory.LaurentSeries

import Theorems.FLT.Thm_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_hasRamBound

noncomputable section

open AlgebraicCurve

namespace CD

section Transport

variable {K : Type*} [Field K]

theorem hasRamBound_puiseuxRamEmb {e : ℕ} (he : 0 < e) (x : LaurentSeries K) :
    HahnSeries.HasRamBound e (HahnSeries.puiseuxRamEmb he x) := by
  intro q hq
  have hq' : q ∈ ⇑(HahnSeries.ramScale e) '' x.support := by
    simpa [HahnSeries.puiseuxRamEmb, HahnSeries.embDomainRingHom] using
      HahnSeries.support_embDomain_subset hq
  obtain ⟨k, -, rfl⟩ := hq'
  exact ⟨k, rfl⟩

theorem order_puiseuxRamEmb {e : ℕ} (he : 0 < e) (x : LaurentSeries K) :
    (HahnSeries.puiseuxRamEmb he x).order = HahnSeries.ramScale e x.order := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hx' : HahnSeries.puiseuxRamEmb (K := K) he x ≠ 0 := by
      intro h0
      exact hx ((HahnSeries.puiseuxRamEmb (K := K) he).injective (by rw [h0, map_zero]))
    have h2 : (HahnSeries.puiseuxRamEmb (K := K) he x).orderTop
        = WithTop.map (⇑(HahnSeries.ramScale e)) x.orderTop :=
      HahnSeries.orderTop_embDomain
    have h1 := HahnSeries.order_eq_orderTop_of_ne_zero hx'
    rw [h2, ← HahnSeries.order_eq_orderTop_of_ne_zero hx, WithTop.map_coe] at h1
    exact_mod_cast h1

theorem laurentAlgebraMap_eq_C (c : K) :
    algebraMap K (LaurentSeries K) c = HahnSeries.C c := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply]
  simp [HahnSeries.ofPowerSeries_C]

theorem hahnQAlgebraMap_eq_C (c : K) :
    algebraMap K (HahnSeries ℚ K) c = HahnSeries.C c := by
  rw [HahnSeries.algebraMap_apply']
  simp [HahnSeries.ofPowerSeries_C]

end Transport

section Lift

variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]

def liftToHahn (ι : F →ₐ[K] LaurentSeries K) : F →ₐ[K] HahnSeries ℚ K where
  toRingHom := (HahnSeries.puiseuxRamEmb one_pos).comp ι.toRingHom
  commutes' := by
    intro c
    show HahnSeries.puiseuxRamEmb one_pos (ι (algebraMap K F c))
        = algebraMap K (HahnSeries ℚ K) c
    rw [ι.commutes c, laurentAlgebraMap_eq_C, hahnQAlgebraMap_eq_C]
    exact HahnSeries.embDomainRingHom_C

@[scoped simp] theorem liftToHahn_apply (ι : F →ₐ[K] LaurentSeries K) (x : F) :
    liftToHahn ι x = HahnSeries.puiseuxRamEmb one_pos (ι x) := rfl

theorem order_liftToHahn (ι : F →ₐ[K] LaurentSeries K) (x : F) :
    (liftToHahn ι x).order = ((ι x).order : ℚ) := by
  rw [liftToHahn_apply, order_puiseuxRamEmb one_pos, HahnSeries.ramScale_apply]
  simp

end Lift

section Generic

variable (K : Type*) [Field K]

private theorem _root_.AlgebraicCurve.Place.exists_ord_mul_eq_order_of_algHom_laurentSeries {F : Type*} [Field F] [Algebra K F] (ι : F →ₐ[K] LaurentSeries K)
    (h : ∃ x : F, (ι x).order ≠ 0) :
    ∃ (w : Place K F) (γ : ℕ), 0 < γ ∧ ∀ x : F, w.ord x * (γ : ℤ) = (ι x).order := by
  obtain ⟨x₀, hx₀⟩ := h
  have hnt : ∃ x : F, ((liftToHahn ι) x).order ≠ 0 :=
    ⟨x₀, by rw [order_liftToHahn]; exact_mod_cast hx₀⟩
  have hRB : ∀ x : F, HahnSeries.HasRamBound 1 ((liftToHahn ι) x) :=
    fun x => hasRamBound_puiseuxRamEmb one_pos (ι x)
  obtain ⟨w, g, hg, hgw⟩ :=
    Place.exists_ord_mul_eq_order_of_hasRamBound (liftToHahn ι) one_pos hRB hnt
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have hordπ : w.ord (π : F) = 1 := w.ord_coe_irreducible hπ
  have hgval : g = ((ι (π : F)).order : ℚ) := by
    have h1 := hgw (π : F)
    rw [hordπ, order_liftToHahn] at h1
    simpa using h1
  have hpos : 0 < (ι (π : F)).order := by
    rw [hgval] at hg
    exact_mod_cast hg
  refine ⟨w, ((ι (π : F)).order).toNat, by omega, fun x => ?_⟩
  have h1 := hgw x
  rw [hgval, order_liftToHahn] at h1
  have h2 : w.ord x * (ι (π : F)).order = (ι x).order := by exact_mod_cast h1
  rw [Int.toNat_of_nonneg hpos.le]
  exact h2

end Generic

end CD

open AlgebraicCurve.Place

theorem solution (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] (ι : F →ₐ[K] LaurentSeries K)
    (h : ∃ x : F, (ι x).order ≠ 0) :
    ∃ (w : Place K F) (γ : ℕ), 0 < γ ∧ ∀ x : F, w.ord x * (γ : ℤ) = (ι x).order :=
  AlgebraicCurve.Place.exists_ord_mul_eq_order_of_algHom_laurentSeries K ι h

end
