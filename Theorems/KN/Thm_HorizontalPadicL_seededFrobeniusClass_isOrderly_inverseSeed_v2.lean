module

public import Definitions.KN.Def_KN_SeededPrimeGaloisDataV2
public import Definitions.KN.Def_KN_InverseSeedConventionV2

section privateSection

open HorizontalPadicL

private lemma padicComplex_norm_add_eq_left_of_lt
    {p : ℕ} [Fact p.Prime] {x y : ℂ_[p]} (h : ‖y‖ < ‖x‖) :
    ‖x + y‖ = ‖x‖ :=
  (PadicComplex.isNonarchimedean p).add_eq_left_of_lt norm_neg h

private lemma padicComplex_norm_sub_one_eq_one_of_order_coprime
    {p d : ℕ} [Fact p.Prime] (x : ℂ_[p])
    (hd : 2 ≤ d) (hxorder : orderOf x = d) (hcop : Nat.Coprime d p) :
    ‖x - 1‖ = 1 := by
  have hd0 : d ≠ 0 := by omega
  have hxpow : x ^ d = 1 := by
    rw [← hxorder]
    exact pow_orderOf_eq_one x
  have hxnorm : ‖x‖ = 1 := by
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg x) hd0).mp
    rw [← norm_pow, hxpow, norm_one]
  have hxne : x ≠ 1 := by
    intro hx
    have : d = 1 := by simpa [hx] using hxorder.symm
    omega
  have hsuble : ‖x - 1‖ ≤ 1 := by
    simpa [sub_eq_add_neg, hxnorm] using PadicComplex.isNonarchimedean p x (-1)
  apply le_antisymm hsuble
  apply le_of_not_gt
  intro hsub
  have hgeom_le : ∀ n : ℕ, ‖∑ i ∈ Finset.range n, x ^ i‖ ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n hn =>
        rw [Finset.sum_range_succ]
        exact (PadicComplex.isNonarchimedean p _ _).trans
          (max_le hn (by simp [norm_pow, hxnorm]))
  have hpow_sub : ∀ i : ℕ, ‖x ^ i - 1‖ < 1 := by
    intro i
    rw [← geom_sum_mul x i, norm_mul]
    calc
      ‖∑ j ∈ Finset.range i, x ^ j‖ * ‖x - 1‖
          ≤ 1 * ‖x - 1‖ :=
            mul_le_mul_of_nonneg_right (hgeom_le i) (norm_nonneg _)
      _ < 1 := by simpa
  have hsum_sub : ∀ n : ℕ, ‖∑ i ∈ Finset.range n, (x ^ i - 1)‖ < 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n hn =>
        rw [Finset.sum_range_succ]
        exact (PadicComplex.isNonarchimedean p _ _).trans_lt
          (max_lt hn (hpow_sub n))
  have hdnorm : ‖(d : ℂ_[p])‖ = 1 := by
    calc
      ‖(d : ℂ_[p])‖ = ‖((d : ℚ_[p]) : ℂ_[p])‖ := by norm_num
      _ = ‖(d : ℚ_[p])‖ := PadicComplex.norm_extends' p _
      _ = 1 := Padic.norm_natCast_eq_one_iff.mpr hcop.symm
  let S : ℂ_[p] := ∑ i ∈ Finset.range d, x ^ i
  have hSsub : ‖S - d‖ < 1 := by
    have hident : S - (d : ℂ_[p]) = ∑ i ∈ Finset.range d, (x ^ i - 1) := by simp [S]
    grind
  have hSnorm : ‖S‖ = 1 := by
    calc
      ‖S‖ = ‖(S - d) + d‖ := by ring_nf
      _ = ‖(d : ℂ_[p])‖ := by
        rw [add_comm]
        exact padicComplex_norm_add_eq_left_of_lt (by grind)
      _ = 1 := hdnorm
  have hSzero : S = 0 := by
    simp [S, geom_sum_eq hxne, hxpow]
  grind [norm_zero]

theorem solution
    {N k p m B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {f : MTT.Eigenform N k ι} {η : DirichletCharacterWithLevel}
    {V : SeededEigenformPadicPlaceData (p := p) f η}
    (D : SeededOrderlyFrobeniusClassData f η m B V)
    (hηorder : 2 ≤ orderOf η.2)
    (horderCoprime : Nat.Coprime (orderOf η.2) p) :
    ∀ ⦃ℓ : ℕ⦄, ℓ ∈ D.primes →
      IsOrderlyPrimeForSeededEigenformV3 p m V.embedding f η ℓ := by
  intro ℓ hℓ
  refine ⟨D.prime_of_mem hℓ, D.congruent_one_mod_pm hℓ,
    D.coprime_level_seed hℓ, ?_⟩
  let z : ℂ_[p] := V.embedding (η.2 ℓ)
  let a : ℂ_[p] := V.embedding (f.coeff ℓ)
  let e : ℂ_[p] := V.embedding (f.epsilon ℓ)
  have hzorder : orderOf z = orderOf η.2 := by
    exact (orderOf_injective V.embedding.toMonoidHom V.embedding.injective (η.2 ℓ)).trans
      (D.seed_value_has_full_order hℓ)
  have hzsub : ‖z - 1‖ = 1 :=
    padicComplex_norm_sub_one_eq_one_of_order_coprime z hηorder hzorder
      horderCoprime
  have hznorm : ‖z‖ = 1 := by
    have hzpow : z ^ orderOf η.2 = 1 := by
      rw [← hzorder]
      exact pow_orderOf_eq_one z
    have hd0' : orderOf η.2 ≠ 0 := by omega
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg z) hd0').mp
    rw [← norm_pow, hzpow, norm_one]
  have ha : ‖a - 2‖ < 1 := by
    simpa [a, map_sub, map_ofNat] using D.coeff_near_two hℓ
  have he : ‖e - 1‖ < 1 := by
    simpa [e, map_sub, map_one] using D.nebentype_near_one hℓ
  let u : ℂ_[p] := 2 * z - 1 - z ^ 2
  let err : ℂ_[p] := z * (a - 2) - (e - 1)
  have hu : ‖u‖ = 1 := by
    have huident : u = -(z - 1) ^ 2 := by grind
    simp_all
  have herr : ‖err‖ < 1 := by
    have h₁ : ‖z * (a - 2)‖ < 1 := by simp [norm_mul, hznorm, ha]
    have h₂ : ‖(e - 1)‖ < 1 := by simp [he]
    simp only [err]
    rw [sub_eq_add_neg]
    exact (PadicComplex.isNonarchimedean p _ _).trans_lt (by grind [norm_neg])
  have htarget : z * a - z ^ 2 - e = u + err := by grind
  simp only [map_sub, map_mul, map_pow]
  change ‖z * a - z ^ 2 - e‖ = 1
  rw [htarget]
  exact (padicComplex_norm_add_eq_left_of_lt (by grind)).trans hu

end privateSection

public section publicSection

namespace HorizontalPadicL

theorem seededFrobeniusClass_isOrderly_inverseSeed_v2
    {N k p m B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {f : MTT.Eigenform N k ι} {η : DirichletCharacterWithLevel}
    {V : SeededEigenformPadicPlaceData (p := p) f η}
    (D : SeededOrderlyFrobeniusClassData f η m B V)
    (hηorder : 2 ≤ orderOf η.2)
    (horderCoprime : Nat.Coprime (orderOf η.2) p) :
    ∀ ⦃ℓ : ℕ⦄, ℓ ∈ D.primes →
      IsOrderlyPrimeForSeededEigenformV3 p m V.embedding f η ℓ := _root_.solution D hηorder horderCoprime

end HorizontalPadicL

end publicSection
