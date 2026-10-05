module

public import Definitions.FLT.Def_ModularCurve_X0
public import Definitions.FLT.Def_ModularCurve_PhiGen

import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PhiGen_splits_of_coeff_evalAtJ_eq

noncomputable section

open Polynomial

namespace ModularCurve
p2m_export "ModularCurve" "qExpand evalAtJ ModularPolynomialData coeffEmb"
p2m_open "ModularCurve"
namespace PhiGen
p2m_export "ModularCurve.PhiGen" "conj phiProd PhiGenDescends"
p2m_open "ModularCurve.PhiGen"

section Splitting

variable {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)]
variable (ζ : Kˣ) {c : ℕ → LaurentSeries ℚ}

private theorem splits_of_coeff_evalAtJ_eq (hc : PhiGenDescends ℓ ζ c)
    (data : ModularPolynomialData ℓ)
    (hcoeff : ∀ k, evalAtJ (data.Φ.coeff k) = c k) :
    data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ) = phiProd ℓ (conj ℓ ζ) := by
  refine Polynomial.ext fun k => ?_
  rw [Polynomial.coeff_map, RingHom.comp_apply, RingHom.comp_apply, hcoeff k, hc k]

end Splitting

end PhiGen
end ModularCurve

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_PhiGen_splits_of_coeff_evalAtJ_eq.ModularCurve _root_.ModularCurve.PhiGen _root_.P2MW.S_ModularCurve_PhiGen_splits_of_coeff_evalAtJ_eq.ModularCurve.PhiGen in

theorem solution {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) {c : ℕ → LaurentSeries ℚ} (hc : PhiGenDescends ℓ ζ c) (data : ModularPolynomialData ℓ) (hcoeff : ∀ k, evalAtJ (data.Φ.coeff k) = c k) : data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ) = phiProd ℓ (conj ℓ ζ) :=
  ModularCurve.PhiGen.splits_of_coeff_evalAtJ_eq ζ hc data hcoeff

end S_ModularCurve_PhiGen_splits_of_coeff_evalAtJ_eq
end P2MW
export P2MW.S_ModularCurve_PhiGen_splits_of_coeff_evalAtJ_eq (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.splits_of_coeff_evalAtJ_eq {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) {c : ℕ → LaurentSeries ℚ} (hc : PhiGenDescends ℓ ζ c) (data : ModularPolynomialData ℓ) (hcoeff : ∀ k, evalAtJ (data.Φ.coeff k) = c k) : data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ) = phiProd ℓ (conj ℓ ζ) := _root_.P2MW.S_ModularCurve_PhiGen_splits_of_coeff_evalAtJ_eq.solution ζ hc data hcoeff

end publicSection
