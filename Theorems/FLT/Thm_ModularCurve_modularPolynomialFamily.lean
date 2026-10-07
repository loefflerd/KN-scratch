module

public import Definitions.FLT.Def_ModularCurve_X0
public import Definitions.FLT.Def_ModularCurve_PhiGen

import Theorems.FLT.Thm_ModularCurve_PhiGen_exists_phiGenDescends
import Theorems.FLT.Thm_ModularCurve_PhiGen_PhiGenDescends_intCoeffs
import Theorems.FLT.Thm_ModularCurve_PhiGen_mem_adjoin_jq_of_phiGenDescends
import Theorems.FLT.Thm_ModularCurve_PhiGen_exists_modularPolynomialData_coeff_eq
import Theorems.FLT.Thm_ModularCurve_PhiGen_evalSymm_of_coeff_evalAtJ_eq
import Mathlib.NumberTheory.Cyclotomic.Basic
import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_modularPolynomialFamily
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "jq ModularPolynomialData EvalSymm ModularPolynomialFamily PhiGen.IntCoeffs PhiGen.exists_phiGenDescends PhiGen.mem_adjoin_jq_of_phiGenDescends PhiGen.exists_modularPolynomialData_coeff_eq PhiGen.evalSymm_of_coeff_evalAtJ_eq"
p2m_open "ModularCurve"

theorem exists_modularPolynomialData_evalSymm' (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] :
    ∃ data : ModularPolynomialData ℓ, EvalSymm data.Φ := by
  have : NeZero ((ℓ : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hℓ.out.ne_zero⟩
  have hcyc : IsCyclotomicExtension {ℓ} ℚ (CyclotomicField ℓ ℚ) :=
    CyclotomicField.isCyclotomicExtension (n := ℓ) (K := ℚ)
  have : FiniteDimensional ℚ (CyclotomicField ℓ ℚ) :=
    IsCyclotomicExtension.finiteDimensional {ℓ} ℚ (CyclotomicField ℓ ℚ)
  have : IsGalois ℚ (CyclotomicField ℓ ℚ) :=
    IsCyclotomicExtension.isGalois (S := {ℓ}) (K := ℚ) (L := CyclotomicField ℓ ℚ)
  obtain ⟨z, hz⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField ℓ ℚ)
    (Set.mem_singleton ℓ) hℓ.out.ne_zero
  have hzu : IsUnit z := hz.isUnit hℓ.out.ne_zero
  have hζ : IsPrimitiveRoot ((hzu.unit : (CyclotomicField ℓ ℚ)ˣ) : CyclotomicField ℓ ℚ) ℓ := by
    rw [hzu.unit_spec]; exact hz
  have hζ1 : hzu.unit ^ ℓ = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one]
  obtain ⟨c, hc⟩ := PhiGen.exists_phiGenDescends ℓ hzu.unit hζ
  have hint : ∀ k, PhiGen.IntCoeffs (c k) := fun k => hc.intCoeffs hζ1 k
  have hmem : ∀ k, c k ∈ Algebra.adjoin ℚ {jq} :=
    fun k => PhiGen.mem_adjoin_jq_of_phiGenDescends ℓ hzu.unit hζ c hc k
  obtain ⟨data, hcoeff⟩ := PhiGen.exists_modularPolynomialData_coeff_eq hc hint hmem
  exact ⟨data, PhiGen.evalSymm_of_coeff_evalAtJ_eq hζ hc data hcoeff⟩

theorem modularPolynomialFamily' : ModularPolynomialFamily :=
  fun ℓ _ hℓ => by
    have : Fact (Nat.Prime ℓ) := ⟨hℓ⟩
    exact exists_modularPolynomialData_evalSymm' ℓ

end ModularCurve

end

theorem solution : ModularCurve.ModularPolynomialFamily := ModularCurve.modularPolynomialFamily'

end S_ModularCurve_modularPolynomialFamily
end P2MW
export P2MW.S_ModularCurve_modularPolynomialFamily (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.modularPolynomialFamily : ModularPolynomialFamily := _root_.P2MW.S_ModularCurve_modularPolynomialFamily.solution

end publicSection
