import Mathlib
import Definitions.FLT.Def_WeierstrassCurve_GenusOnePic0
import Definitions.FLT.Def_WeierstrassCurve_GenusOnePlaceGateCentred
import Theorems.FLT.Thm_WeierstrassCurve_Affine_placeOfPoint_some_eq_ofHeightOneSpectrum
import Theorems.FLT.Thm_P2M_Dup_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_isMaximal
import Theorems.FLT.Thm_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_ne_bot
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_GenusOnePlaceGate_ext_of_isCentred
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"

set_option autoImplicit false

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine

universe u

theorem solution
    {F : Type u} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}
    [IsDedekindDomain W.CoordinateRing]
    (g₁ g₂ : WeierstrassCurve.Affine.GenusOnePlaceGate W)
    (h₁ : @WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred F _ W g₁)
    (h₂ : @WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred F _ W g₂) :
    g₁ = g₂ := by

  have hw : ∀ {x y : F} (h : W.Nonsingular x y),
      ∃ w : IsDedekindDomain.HeightOneSpectrum W.CoordinateRing,
        w.asIdeal = CoordinateRing.XYIdeal W x (Polynomial.C y) := fun {x y} h =>
    ⟨⟨CoordinateRing.XYIdeal W x (Polynomial.C y),
        (CoordinateRing.XYIdeal_isMaximal h.left).isPrime,
        CoordinateRing.XYIdeal_ne_bot x (Polynomial.C y)⟩, rfl⟩

  have hsome : ∀ {x y : F} (h : W.Nonsingular x y),
      g₁.pointEquivPlace (Point.some x y h) = g₂.pointEquivPlace (Point.some x y h) := by
    intro x y h
    obtain ⟨w, hw⟩ := hw h
    have e1 := @placeOfPoint_some_eq_ofHeightOneSpectrum F _ _ W g₁ h₁ _ x y h w hw
    have e2 := @placeOfPoint_some_eq_ofHeightOneSpectrum F _ _ W g₂ h₂ _ x y h w hw
    exact e1.trans e2.symm

  have hall : ∀ P : W.Point, g₁.pointEquivPlace P = g₂.pointEquivPlace P := by
    intro P
    cases P with
    | some x y h => exact hsome h
    | zero =>
      have key : g₁.pointEquivPlace.symm (g₂.pointEquivPlace 0) = 0 := by
        rcases hP : g₁.pointEquivPlace.symm (g₂.pointEquivPlace 0) with _ | ⟨x, y, h⟩
        · rfl
        · exfalso
          have h3 : g₂.pointEquivPlace 0 = g₁.pointEquivPlace (Point.some x y h) := by
            rw [← hP, Equiv.apply_symm_apply]
          have h5 : (Point.some x y h : W.Point) = 0 :=
            g₂.pointEquivPlace.injective ((h3.trans (hsome h)).symm)
          exact Point.some_ne_zero h h5
      have := congrArg g₁.pointEquivPlace key
      rw [Equiv.apply_symm_apply] at this
      first
        | exact this.symm



  cases g₁ with
  | mk e₁ d₁ =>
    cases g₂ with
    | mk e₂ d₂ =>
      congr
      exact Equiv.ext hall

end S_WeierstrassCurve_Affine_GenusOnePlaceGate_ext_of_isCentred
end P2MW
export P2MW.S_WeierstrassCurve_Affine_GenusOnePlaceGate_ext_of_isCentred (solution)
