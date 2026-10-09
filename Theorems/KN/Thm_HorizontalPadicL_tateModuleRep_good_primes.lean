module

public import Definitions.KN.Def_KN_EllipticCurveAttachedEigenform
public import Definitions.FLT.Def_EllipticCurve_TateModule
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix

import Theorems.KN.Thm_HorizontalPadicL_exists_good_integral_model_with_ap
import Theorems.FLT.Thm_WeierstrassCurve_exists_addEquiv_point_of_variableChange_eq
import Theorems.FLT.Thm_TateModule_exists_linearMap_apply_eq_of_addMonoidHom
import Theorems.FLT.Thm_WeierstrassCurve_tateModuleRep_isUnramifiedAt_of_isGoodPrimeFor
import Theorems.FLT.Thm_WeierstrassCurve_tateModuleRep_charpoly_frobenius
import Theorems.FLT.Thm_WeierstrassCurve_card_torsionBy_eq_sq_of_isAlgClosed

section privateSection

namespace TateModelTransferAux

noncomputable def torsionEquiv {M N : Type} [AddCommGroup M] [AddCommGroup N]
    (e : M ≃+ N) (n : ℤ) :
    Submodule.torsionBy ℤ M n ≃ Submodule.torsionBy ℤ N n where
  toFun x := ⟨e x, by
    have hx : n • (x : M) = 0 := x.property
    change n • e x = 0
    rw [← map_zsmul, hx, map_zero]⟩
  invFun x := ⟨e.symm x, by
    change n • e.symm x = 0
    have hx : n • (x : N) = 0 := x.property
    rw [← map_zsmul, hx, map_zero]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)

lemma exists_tateEquiv {M N G : Type} [AddCommGroup M] [AddCommGroup N]
    [Monoid G] [DistribMulAction G M] [DistribMulAction G N]
    (p : ℕ) [Fact p.Prime] (e : M ≃+ N)
    (he : ∀ (g : G) x, e (g • x) = g • e x) :
    ∃ T : TateModule p M ≃ₗ[ℤ_[p]] TateModule p N,
      ∀ g x, T (TateModule.rep p M G g x) = TateModule.rep p N G g (T x) := by
  obtain ⟨P, hP, -⟩ := TateModule.exists_linearMap_apply_eq_of_addMonoidHom p e.toAddMonoidHom
  obtain ⟨Q, hQ, -⟩ :=
    TateModule.exists_linearMap_apply_eq_of_addMonoidHom p e.symm.toAddMonoidHom
  have hQP : Q ∘ₗ P = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext n
    rw [LinearMap.comp_apply, hQ, hP, LinearMap.id_apply]
    exact e.symm_apply_apply _
  have hPQ : P ∘ₗ Q = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext n
    rw [LinearMap.comp_apply, hP, hQ, LinearMap.id_apply]
    exact e.apply_symm_apply _
  refine ⟨LinearEquiv.ofLinearMap P Q hPQ hQP, ?_⟩
  intro g x
  apply Subtype.ext
  funext n
  change ((P (TateModule.rep p M G g x) : TateModule p N) : ℕ → N) n =
    ((TateModule.rep p N G g (P x) : TateModule p N) : ℕ → N) n
  rw [hP, TateModule.rep_apply, TateModule.rep_apply, hP]
  exact he g _

end TateModelTransferAux

namespace HorizontalPadicL

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

/-- The fixed Tate-module representation of the original rational curve has the
expected good-prime properties; the auxiliary integral model may vary with the prime. -/
theorem good_primes_of_card (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hmod : IsModular E) (p : ℕ) [Fact p.Prime]
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ
      (E⁄(AlgebraicClosure ℚ)).Point ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ 2)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hN : ¬ ℓ ∣ modularConductor E hmod) (hℓp : ℓ ≠ p) :
    (E.tateModuleRep p hcard).IsUnramifiedAt ℓ ∧
      ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
        LinearMap.charpoly ((E.tateModuleRep p hcard).ρ σ) =
          X ^ 2 - C ((E.LFunction ℓ : ℤ) : ℤ_[p]) * X + C ((ℓ : ℕ) : ℤ_[p]) := by
  classical
  obtain ⟨W, ⟨D, hD⟩, hgood, hap⟩ := exists_good_integral_model_with_ap E hmod ℓ hℓ hN
  obtain ⟨e, he⟩ := exists_addEquiv_point_of_variableChange_eq (AlgebraicClosure ℚ) D hD
  have hWcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point
        ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ 2 := by
    intro n
    rw [← Nat.card_congr (TateModelTransferAux.torsionEquiv e ((p ^ n : ℕ) : ℤ))]
    exact hcard n
  obtain ⟨T, hT⟩ := TateModelTransferAux.exists_tateEquiv p e he
  let R := E.tateModuleRep p hcard
  let S := (W.map (Int.castRingHom ℚ)).tateModuleRep p hWcard
  let : Module.Free ℤ_[p] (TateModule p (E⁄(AlgebraicClosure ℚ)).Point) := R.instFree
  let : Module.Finite ℤ_[p] (TateModule p (E⁄(AlgebraicClosure ℚ)).Point) := R.instFinite
  let : Module.Free ℤ_[p]
      (TateModule p ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) := S.instFree
  let : Module.Finite ℤ_[p]
      (TateModule p ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) := S.instFinite
  have hinter (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : R.V) :
      T (R.ρ σ x) = S.ρ σ (T x) := hT σ x
  constructor
  · intro A hA σ hσ
    have hu := tateModuleRep_isUnramifiedAt_of_isGoodPrimeFor W p hWcard hℓ hℓp hgood
    have hS : S.ρ σ = 1 := hu A hA σ hσ
    apply LinearMap.ext
    intro x
    apply T.injective
    rw [hinter, hS]
    rfl
  · intro A hA σ hσ
    have hconj : T.conj (R.ρ σ) = S.ρ σ := by
      apply LinearMap.ext
      intro x
      change T (R.ρ σ (T.symm x)) = S.ρ σ x
      exact (hT σ (T.symm x)).trans (congrArg (S.ρ σ) (T.apply_symm_apply x))
    have hchar := tateModuleRep_charpoly_frobenius W p hWcard ℓ hℓ hgood hℓp A hA σ hσ
    rw [hap] at hchar
    exact (T.charpoly_conj (R.ρ σ)).symm.trans
      ((congrArg LinearMap.charpoly hconj).trans hchar)

end HorizontalPadicL

end privateSection

public section publicSection

namespace HorizontalPadicL

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

/-- One fixed Tate-module representation of `E` is unramified outside the modular
conductor and `p`, with the expected Frobenius characteristic polynomial there.
The integral good-reduction models used to prove this may depend on the prime. -/
theorem tateModuleRep_good_primes (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hmod : IsModular E) (p : ℕ) [Fact p.Prime] :
    ∃ hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ
        (E⁄(AlgebraicClosure ℚ)).Point ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ 2,
      ∀ (ℓ : ℕ), ℓ.Prime → ¬ ℓ ∣ modularConductor E hmod → ℓ ≠ p →
        (E.tateModuleRep p hcard).IsUnramifiedAt ℓ ∧
          ∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
            ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
              LinearMap.charpoly ((E.tateModuleRep p hcard).ρ σ) =
                X ^ 2 - C ((E.LFunction ℓ : ℤ) : ℤ_[p]) * X + C ((ℓ : ℕ) : ℤ_[p]) := by
  classical
  have : (E.baseChange (AlgebraicClosure ℚ)).IsElliptic :=
    ⟨by simpa only [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ] using
      E.isUnit_Δ.map (algebraMap ℚ (AlgebraicClosure ℚ))⟩
  have hcard (n : ℕ) : Nat.card (Submodule.torsionBy ℤ
      (E⁄(AlgebraicClosure ℚ)).Point ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ 2 := by
    have hn : ((p ^ n : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by
      exact_mod_cast pow_ne_zero n (Nat.Prime.ne_zero (Fact.out : p.Prime))
    exact card_torsionBy_eq_sq_of_isAlgClosed (E.baseChange (AlgebraicClosure ℚ)) hn
  exact ⟨hcard, good_primes_of_card E hmod p hcard⟩

end HorizontalPadicL

end publicSection
