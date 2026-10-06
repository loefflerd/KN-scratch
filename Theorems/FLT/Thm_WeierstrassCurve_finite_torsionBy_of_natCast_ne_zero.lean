module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

import Mathlib.Algebra.Order.Star.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Theorems.FLT.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_finite_torsionBy_of_natCast_ne_zero

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution (k : Type*) [Field k] [DecidableEq k] (W : WeierstrassCurve k) [W.IsElliptic]
    (n : ℕ) (hn : (n : k) ≠ 0) :
    Finite (Submodule.torsionBy ℤ W.toAffine.Point n) := by
  classical
  let K := AlgebraicClosure k
  have hnK : (n : K) ≠ 0 := by
    rw [← map_natCast (algebraMap k K) n]
    exact (map_ne_zero _).mpr hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (by simp)
  have hcard : Nat.card (Submodule.torsionBy ℤ (W⁄K).Point n) = n ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed (K := K) W hnK
  have : Finite (Submodule.torsionBy ℤ (W⁄K).Point n) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hn0)
  let φ : (W.toAffine⁄k).Point →+ (W.toAffine⁄K).Point := Point.baseChange k K
  have hφ : Function.Injective φ := Point.map_injective _
  have hmem : ∀ P : Submodule.torsionBy ℤ W.toAffine.Point n, φ P.1 ∈ Submodule.torsionBy ℤ (W⁄K).Point n := by
    intro P
    have hP := P.2
    rw [Submodule.mem_torsionBy_iff] at hP ⊢
    show (n : ℤ) • φ P.1 = 0
    rw [← map_zsmul φ]
    exact (congrArg φ hP).trans (map_zero φ)
  refine Finite.of_injective (fun P => (⟨φ P.1, hmem P⟩ : Submodule.torsionBy ℤ (W⁄K).Point n)) ?_
  intro P Q h
  exact Subtype.ext (hφ (congrArg Subtype.val h))

end S_WeierstrassCurve_finite_torsionBy_of_natCast_ne_zero
end P2MW
export P2MW.S_WeierstrassCurve_finite_torsionBy_of_natCast_ne_zero (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem WeierstrassCurve.finite_torsionBy_of_natCast_ne_zero (k : Type*) [Field k] [DecidableEq k] (W : WeierstrassCurve k) [W.IsElliptic]
    (n : ℕ) (hn : (n : k) ≠ 0) :
    Finite (Submodule.torsionBy ℤ W.toAffine.Point n) := _root_.P2MW.S_WeierstrassCurve_finite_torsionBy_of_natCast_ne_zero.solution k W n hn

end publicSection
