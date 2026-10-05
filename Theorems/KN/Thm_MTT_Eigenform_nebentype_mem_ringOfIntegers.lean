module

public import Definitions.KN.Def_MTT_EigenformCoefficientField
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.RingTheory.RootsOfUnity.Minpoly

section privateSection

noncomputable section

theorem solution
    {N k : ℕ} {ι : MTT.Qbar →+* ℂ} (f : MTT.Eigenform N k ι)
    (a : ZMod N) :
    (⟨f.epsilon a, f.nebentype_mem_coefficientField a⟩ : f.coefficientField) ∈
      integralClosure ℤ f.coefficientField := by
  rw [mem_integralClosure_iff]
  let inclQ : f.coefficientField →ₐ[ℚ] MTT.Qbar :=
    f.coefficientField.subtype.toRatAlgHom
  let inclZ : f.coefficientField →ₐ[ℤ] MTT.Qbar := inclQ.restrictScalars ℤ
  apply (isIntegral_algHom_iff inclZ inclZ.injective).mp
  change IsIntegral ℤ (f.epsilon a)
  by_cases ha : f.epsilon a = 0
  · simpa [ha] using (isIntegral_zero : IsIntegral ℤ (0 : MTT.Qbar))
  · have hu : IsUnit a := MulChar.apply_ne_zero_iff.mp ha
    let := Fintype.ofFinite (ZMod N)ˣ
    let d := Fintype.card (ZMod N)ˣ
    have hd : 0 < d := Fintype.card_pos
    have hroot := f.epsilon.apply_mem_rootsOfUnity hu.unit
    have hpow : (f.epsilon a) ^ d = 1 := by
      simpa [IsUnit.unit_spec hu] using (mem_rootsOfUnity' d _).mp hroot
    refine ⟨Polynomial.X ^ d - 1,
      Polynomial.monic_X_pow_sub_C 1 (Nat.ne_of_gt hd), ?_⟩
    simp [hpow]
end

end privateSection

public section publicSection

noncomputable section

/-- Every nebentype value, regarded as an element of the coefficient field,
belongs to its ring of integers. -/
theorem MTT.Eigenform.nebentype_mem_ringOfIntegers
    {N k : ℕ} {ι : MTT.Qbar →+* ℂ} (f : MTT.Eigenform N k ι)
    (a : ZMod N) :
    (⟨f.epsilon a, f.nebentype_mem_coefficientField a⟩ : f.coefficientField) ∈
      integralClosure ℤ f.coefficientField := _root_.solution f a
end

end publicSection
