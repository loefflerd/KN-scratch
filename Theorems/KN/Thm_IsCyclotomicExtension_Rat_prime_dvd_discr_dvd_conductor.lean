module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

public noncomputable section

/-- Every rational prime dividing the discriminant of an `n`-th cyclotomic
field divides `n`. -/
theorem IsCyclotomicExtension.Rat.prime_dvd_discr_dvd_conductor
    (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K]
    {l : ℕ} (hl : l.Prime)
    (hldisc : (l : ℤ) ∣ NumberField.discr K) : l ∣ n := by
  have hnat : l ∣ (NumberField.discr K).natAbs :=
    Int.natAbs_dvd_natAbs.mpr hldisc
  rw [IsCyclotomicExtension.Rat.natAbs_discr n K] at hnat
  have hden : (∏ q ∈ n.primeFactors, q ^ (n.totient / (q - 1))) ∣ n ^ n.totient :=
    Nat.prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos n)
  have hpow : l ∣ n ^ Nat.totient n :=
    hnat.trans (Nat.div_dvd_of_dvd hden)
  exact hl.dvd_of_dvd_pow hpow

end
