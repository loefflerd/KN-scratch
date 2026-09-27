import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

set_option autoImplicit false
noncomputable section

/-- Every rational prime dividing the discriminant of an `n`-th cyclotomic
field divides `n`. -/
theorem IsCyclotomicExtension.Rat.prime_dvd_discr_dvd_conductor
    (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K]
    {l : ℕ} (hl : l.Prime)
    (hldisc : (l : ℤ) ∣ NumberField.discr K) : l ∣ n := by sorry
