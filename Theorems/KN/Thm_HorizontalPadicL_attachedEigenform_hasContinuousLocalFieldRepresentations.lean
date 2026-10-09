module

public import Definitions.KN.Def_KN_EllipticCurveAttachedEigenform
public import Theorems.KN.Thm_HorizontalPadicL_corollary_5_17_conditional

import Definitions.FLT.Def_EllipticCurve_TateModule
import Theorems.KN.Thm_HorizontalPadicL_tateModuleRep_good_primes
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

section privateSection

namespace EllipticRepresentationAux

open NumberField IsLocalRing IsDedekindDomain Filter
open scoped Topology

lemma integralCoeff_eq (ι : MTT.Qbar →+* ℂ) (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hmod : HorizontalPadicL.IsModular E) (hN : 0 < HorizontalPadicL.modularConductor E hmod)
    (hk : 2 ≤ 2) (n : ℕ) :
    (HorizontalPadicL.attachedEigenform ι E hmod).integralCoeff hN hk n =
      (E.LFunction n : 𝓞 (HorizontalPadicL.attachedEigenform ι E hmod).coefficientField) := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

lemma integralNebentype_eq (ι : MTT.Qbar →+* ℂ) (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hmod : HorizontalPadicL.IsModular E) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hN : ¬ ℓ ∣ HorizontalPadicL.modularConductor E hmod) :
    (HorizontalPadicL.attachedEigenform ι E hmod).integralNebentype
      (ℓ : ZMod (HorizontalPadicL.modularConductor E hmod)) = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  change (1 : DirichletCharacter MTT.Qbar (HorizontalPadicL.modularConductor E hmod))
    (ℓ : ZMod (HorizontalPadicL.modularConductor E hmod)) = 1
  exact MulChar.one_apply ((ZMod.isUnit_prime_iff_not_dvd hℓ).mpr hN)

lemma p_mem_completion_maximal {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p])
    [IsLocalRing (f.coefficientCompletion ιp)] :
    (p : f.coefficientCompletion ιp) ∈ maximalIdeal (f.coefficientCompletion ιp) := by
  let : (f.coefficientPrime ιp).IsPrime := Ideal.IsPrime.comap _
  have hp : f.coefficientReduction ιp (p : f.coefficientCompletion ιp) = 0 := by
    change Ideal.Quotient.mk (f.coefficientPrime ιp) (p : 𝓞 f.coefficientField) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (f.p_mem_coefficientPrime ιp)
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  exact not_isUnit_zero (hp ▸ hu.map (f.coefficientReduction ιp))

lemma coord_mem_ideal {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]
    (b : Module.Basis (Fin 2) R V) (I : Ideal R) {v : V}
    (hv : v ∈ I • (⊤ : Submodule R V)) (i : Fin 2) : b.repr v i ∈ I := by
  refine Submodule.smul_induction_on (p := fun v => b.repr v i ∈ I) hv ?_ ?_
  · intro a ha v _
    simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using I.mul_mem_right (b.repr v i) ha
  · intro v w hv hw
    simpa only [map_add, Finsupp.add_apply] using I.add_mem hv hw

noncomputable def matrixRep {R : Type} [CommRing R] [IsLocalRing R]
    (r : GaloisRepAdic R) (b : Module.Basis (Fin 2) R r.V) :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) R :=
  (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp r.ρ

lemma matrixRep_continuous {R K : Type} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Valued K (WithZero (Multiplicative ℤ))]
    (hval : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) =
      (IsDiscreteValuationRing.maximalIdeal R).valuation K)
    (r : GaloisRepAdic R) (b : Module.Basis (Fin 2) R r.V) :
    Continuous ((algebraMap R K).mapMatrix.toMonoidHom.comp (matrixRep r b)) := by
  classical
  apply continuous_of_continuousAt_one
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  change ContinuousAt (fun σ => algebraMap R K (matrixRep r b σ i j)) 1
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff]
  apply (Valued.hasBasis_nhds_zero K (WithZero (Multiplicative ℤ))).tendsto_right_iff.mpr
  intro γ _
  let emb := MonoidWithZeroHom.ValueGroup₀.embedding
    (f := (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).toMonoidWithZeroHom)
  let γ' : WithZero (Multiplicative ℤ) := emb (γ : _)
  have hγ' : γ' ≠ 0 :=
    (map_ne_zero_iff emb MonoidWithZeroHom.ValueGroup₀.embedding_injective).mpr (Units.ne_zero γ)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, WithZero.exp (-(n : ℤ)) < γ' := by
    refine ⟨(WithZero.log γ').natAbs + 1, ?_⟩
    conv_rhs => rw [← WithZero.exp_log hγ']
    rw [WithZero.exp_lt_exp]
    omega
  obtain ⟨L, hL, hfix⟩ := r.isAdicContinuous n
  let : FiniteDimensional ℚ L := hL
  have hU := L.fixingSubgroup_isOpen.mem_nhds L.fixingSubgroup.one_mem
  filter_upwards [hU] with σ hσ
  have hentry := coord_mem_ideal b (maximalIdeal R ^ n)
    (hfix σ ((L.mem_fixingSubgroup_iff σ).mp hσ) (b j)) i
  have heq : b.repr (r.ρ σ (b j) - b j) i =
      matrixRep r b σ i j - (1 : Matrix (Fin 2) (Fin 2) R) i j := by
    simp [matrixRep, LinearMap.toMatrixAlgEquiv_apply, Matrix.one_apply,
      Finsupp.single_apply, eq_comm]
  rw [heq] at hentry
  have hbound :=
    ((IsDiscreteValuationRing.maximalIdeal R).intValuation_le_pow_iff_mem _ n).mpr hentry
  apply (Valuation.restrict_lt_iff_lt_embedding (Valued.v : Valuation K _)).mpr
  change Valued.v (algebraMap R K (matrixRep r b σ i j) -
    algebraMap R K (matrixRep r b 1 i j)) < γ'
  rw [map_one, ← map_sub, hval, HeightOneSpectrum.valuation_of_algebraMap]
  exact hbound.trans_lt hn

end EllipticRepresentationAux

namespace HorizontalPadicL

open NumberField Polynomial
open EllipticRepresentationAux

theorem representation_solution (ι : MTT.Qbar →+* ℂ) (E : WeierstrassCurve ℚ)
    [E.IsElliptic] (hmod : IsModular E) :
    (attachedEigenform ι E hmod).HasContinuousLocalFieldRepresentations := by
  classical
  constructor
  intro p hp hN hk ιp
  let f := attachedEigenform ι E hmod
  let R := f.coefficientCompletion ιp
  let K := f.coefficientLocalField ιp
  let : IsDomain R := f.coefficientCompletion_isDomain hN hk ιp
  let : IsDiscreteValuationRing R := f.coefficientCompletion_isDiscreteValuationRing hN hk ιp
  let : IsAdicComplete (IsLocalRing.maximalIdeal R) R :=
    f.coefficientCompletion_isAdicComplete hN hk ιp
  let := f.coefficientLocalFieldValued ιp
  let ψ : ℤ_[p] →+* R := GaloisRep.padicIntToRing R p (p_mem_completion_maximal f ιp)
  have hψ : IsLocalHom ψ := GaloisRep.isLocalHom_padicIntToRing R p _
  let : Algebra ℤ_[p] R := ψ.toAlgebra
  obtain ⟨hcard, hgood⟩ := tateModuleRep_good_primes E hmod p
  let r := E.tateModuleRep p hcard
  let s := r.baseChangeAlong ψ hψ
  let b : Module.Basis (Fin 2) R s.V :=
    (Module.finBasis R s.V).reindex (finCongr s.finrank_eq)
  let ρ := (algebraMap R K).mapMatrix.toMonoidHom.comp (matrixRep s b)
  refine ⟨ρ, matrixRep_continuous rfl s b, ?_, ?_⟩
  · intro ℓ hℓ hcop A hA σ hσ
    have hNℓ : ¬ ℓ ∣ modularConductor E hmod :=
      (hℓ.coprime_iff_not_dvd).mp (Nat.coprime_mul_iff_right.mp hcop).1
    have hℓp : ℓ ≠ p := by
      have hnp := (hℓ.coprime_iff_not_dvd).mp (Nat.coprime_mul_iff_right.mp hcop).2
      intro heq
      apply hnp
      rw [← heq]
    have hr := (hgood ℓ hℓ hNℓ hℓp).1 A hA σ hσ
    have hs : s.ρ σ = 1 := by
      change (r.ρ σ).baseChange R = 1
      rw [hr, LinearMap.baseChange_one]
    change (algebraMap R K).mapMatrix ((LinearMap.toMatrixAlgEquiv b) (s.ρ σ)) = 1
    rw [hs, map_one, map_one]
  · intro ℓ hℓ hcop A hA σ hσ
    have hNℓ : ¬ ℓ ∣ modularConductor E hmod :=
      (hℓ.coprime_iff_not_dvd).mp (Nat.coprime_mul_iff_right.mp hcop).1
    have hℓp : ℓ ≠ p := by
      have hnp := (hℓ.coprime_iff_not_dvd).mp (Nat.coprime_mul_iff_right.mp hcop).2
      intro heq
      apply hnp
      rw [← heq]
    have hr := (hgood ℓ hℓ hNℓ hℓp).2 A hA σ hσ
    have hs : LinearMap.charpoly (s.ρ σ) =
        X ^ 2 - C (E.LFunction ℓ : R) * X + C (ℓ : R) := by
      change LinearMap.charpoly ((r.ρ σ).baseChange R) = _
      rw [LinearMap.charpoly_baseChange, hr]
      simp [Polynomial.C_eq_intCast]
    have hm : Matrix.charpoly (ρ σ) =
        X ^ 2 - C (E.LFunction ℓ : K) * X + C (ℓ : K) := by
      change ((LinearMap.toMatrix b b (s.ρ σ)).map (algebraMap R K)).charpoly = _
      rw [Matrix.charpoly_map, LinearMap.charpoly_toMatrix, hs]
      simp [Polynomial.C_eq_intCast]
      exact map_natCast (algebraMap R K) ℓ
    have hcoeff := integralCoeff_eq ι E hmod hN hk ℓ
    have heps := integralNebentype_eq ι E hmod ℓ hℓ hNℓ
    constructor
    · rw [Matrix.trace_eq_neg_charpoly_coeff, hm]
      simp only [hcoeff, map_intCast]
      simp
    · rw [Matrix.det_eq_sign_charpoly_coeff, hm]
      simp only [heps, map_mul, map_pow, map_natCast, map_one]
      simp

end HorizontalPadicL

end privateSection

public section publicSection

namespace HorizontalPadicL

/-- The Tate module supplies all the local-field Galois representations required
by the conditional KN theorem for the eigenform attached to an elliptic curve. -/
theorem attachedEigenform_hasContinuousLocalFieldRepresentations
    (ι : MTT.Qbar →+* ℂ) (E : WeierstrassCurve ℚ) [E.IsElliptic] (hmod : IsModular E) :
    (attachedEigenform ι E hmod).HasContinuousLocalFieldRepresentations :=
  representation_solution ι E hmod

end HorizontalPadicL

end publicSection
