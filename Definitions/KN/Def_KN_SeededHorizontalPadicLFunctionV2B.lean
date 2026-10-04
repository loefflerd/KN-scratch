import Definitions.KN.Def_KN_HorizontalPadicLAux

noncomputable section

namespace HorizontalPadicL

noncomputable def primitiveProductV2
    (χ ψ : DirichletCharacterWithLevel) : DirichletCharacterWithLevel := by
  have : NeZero χ.1.1 := ⟨Nat.ne_of_gt χ.1.2⟩
  have : NeZero ψ.1.1 := ⟨Nat.ne_of_gt ψ.1.2⟩
  have : NeZero (Nat.lcm χ.1.1 ψ.1.1) :=
    ⟨Nat.lcm_ne_zero (Nat.ne_of_gt χ.1.2) (Nat.ne_of_gt ψ.1.2)⟩
  let φ := χ.2.mul ψ.2
  have hφ : φ.conductor ≠ 0 := φ.conductor_ne_zero
  exact ⟨⟨φ.conductor, Nat.pos_of_ne_zero hφ⟩, φ.primitiveCharacter⟩

def trivialCharacterWithLevelV2 : DirichletCharacterWithLevel :=
  ⟨⟨1, Nat.zero_lt_one⟩, 1⟩

def trivialHorizontalCharacterV2 (p : ℕ) [Fact p.Prime] (m : ℕ → ℕ) :
    HorizontalCharacter p m where
  support := ∅
  toMonoidHom := 1

def IsOrderlyPrimeForSeededEigenformV2
    {N k : ℕ} {ι : MTT.Qbar →+* ℂ}
    (p m : ℕ) [Fact p.Prime] (ιp : MTT.Qbar →+* ℂ_[p])
    (f : MTT.Eigenform N k ι) (η : DirichletCharacterWithLevel)
    (ℓ : ℕ) : Prop :=
  ℓ.Prime ∧ Nat.ModEq (p ^ m) ℓ 1 ∧
    Nat.Coprime ℓ (N * η.2.conductor) ∧
    ‖ιp (η.2 ℓ * f.coeff ℓ - 1 - (η.2 ℓ) ^ 2 * f.epsilon ℓ)‖ = 1

structure SeededHorizontalPrimeSystemV2
    {N k : ℕ} {ι : MTT.Qbar →+* ℂ}
    (p : ℕ) [Fact p.Prime] (ιp : MTT.Qbar →+* ℂ_[p])
    (f : MTT.Eigenform N k ι) (η : DirichletCharacterWithLevel) (B : ℕ) where
  orderExponent : ℕ
  orderExponent_pos : 0 < orderExponent
  primeAt : ℕ → ℕ
  primeAt_prime : ∀ n, (primeAt n).Prime
  primeAt_injective : Function.Injective primeAt
  primeAt_avoids : ∀ n, Nat.Coprime (primeAt n) B
  primeAt_orderly : ∀ n,
    IsOrderlyPrimeForSeededEigenformV2 p orderExponent ιp f η (primeAt n)
  naturalDensity : ℝ
  naturalDensity_pos : 0 < naturalDensity
  has_naturalDensity :
    HasPrimeNaturalDensity {ℓ : ℕ | ∃ n : ℕ, primeAt n = ℓ} naturalDensity

def SeededHorizontalPrimeSystemV2.exponent
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeSystemV2 p ιp f η B) (n : ℕ) : ℕ :=
  padicValNat p (L.primeAt n - 1)

structure SeededHorizontalPadicLFunctionV2
    {N k B : ℕ} {ι : MTT.Qbar →+* ℂ} (p : ℕ) [Fact p.Prime]
    (ιp : MTT.Qbar →+* ℂ_[p]) (f : MTT.Eigenform N k ι)
    (η : DirichletCharacterWithLevel) where
  primes : SeededHorizontalPrimeSystemV2 p ιp f η B
  coefficientRing : Subring ℂ_[p]
  coefficient_integral : ∀ x : coefficientRing, (x : ℂ_[p]) ∈ 𝓞_ℂ_[p]
  measure : HorizontalMeasure coefficientRing p primes.exponent

end HorizontalPadicL
