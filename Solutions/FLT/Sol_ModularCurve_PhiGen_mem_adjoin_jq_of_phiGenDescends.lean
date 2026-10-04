import Definitions.FLT.Def_ModularCurve_X0
import Definitions.FLT.Def_ModularCurve_PhiGen
import Definitions.FLT.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.Discriminant
import Theorems.FLT.Thm_ModularCurve_PhiGen_PhiGenDescends_hasSum_cosetPoly_coeff
import Theorems.FLT.Thm_ModularCurve_mem_adjoin_jq_of_hasSum_of_slash_invariant
import Theorems.FLT.Thm_ModularCurve_cosetPoly_smul
import Theorems.FLT.Thm_ModularCurve_E4_cube_div_discriminant_smul
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PhiGen_mem_adjoin_jq_of_phiGenDescends

noncomputable section

open UpperHalfPlane Complex Filter Topology Function Polynomial
open scoped MatrixGroups

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve
p2m_export "ModularCurve" "jq PhiGen.PhiGenDescends PhiGen.PhiGenDescends.hasSum_cosetPoly_coeff mem_adjoin_jq_of_hasSum_of_slash_invariant cosetPoly_smul E4_cube_div_discriminant_smul"
p2m_open "ModularCurve"

section JT

def jt (τ : ℍ) : ℂ := ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

lemma jt_smul (γ : SL(2, ℤ)) (τ : ℍ) : jt (γ • τ) = jt τ :=
  ModularCurve.E4_cube_div_discriminant_smul γ τ

end JT

end ModularCurve

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_PhiGen_mem_adjoin_jq_of_phiGenDescends.ModularCurve ModularCurve.PhiGen in
theorem solution (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : (CyclotomicField ℓ ℚ)ˣ) (hζ : IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ) (c : ℕ → LaurentSeries ℚ) (hc : PhiGenDescends ℓ ζ c) (k : ℕ) : c k ∈ Algebra.adjoin ℚ {jq} := by
  refine ModularCurve.mem_adjoin_jq_of_hasSum_of_slash_invariant (c k) _
    (ModularCurve.PhiGen.PhiGenDescends.hasSum_cosetPoly_coeff ℓ ζ hζ c hc k) fun γ τ => ?_
  exact congrArg (fun p : Polynomial ℂ => p.coeff k)
    (ModularCurve.cosetPoly_smul ℓ hℓ.out ModularCurve.jt ModularCurve.jt_smul γ τ)

end

end S_ModularCurve_PhiGen_mem_adjoin_jq_of_phiGenDescends
end P2MW
export P2MW.S_ModularCurve_PhiGen_mem_adjoin_jq_of_phiGenDescends (solution)
