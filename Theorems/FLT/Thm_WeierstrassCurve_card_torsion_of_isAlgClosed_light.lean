module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Definitions.FLT.Def_FLTPrelim_GaloisRep

import Theorems.FLT.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_card_torsion_of_isAlgClosed_light

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K] [DecidableEq K] (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) : Nat.card (Submodule.torsionBy ℤ (W⁄K).Point n) = n ^ 2 :=
  WeierstrassCurve.card_torsion_of_isAlgClosed W hn

end S_WeierstrassCurve_card_torsion_of_isAlgClosed_light
end P2MW
export P2MW.S_WeierstrassCurve_card_torsion_of_isAlgClosed_light (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.card_torsion_of_isAlgClosed_light {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K] [DecidableEq K] (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) : Nat.card (Submodule.torsionBy ℤ (W⁄K).Point n) = n ^ 2 := _root_.P2MW.S_WeierstrassCurve_card_torsion_of_isAlgClosed_light.solution W hn

end publicSection
