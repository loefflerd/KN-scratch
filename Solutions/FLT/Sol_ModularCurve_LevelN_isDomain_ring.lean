import Definitions.FLT.Def_ModularCurve_LevelNFunctionField
import Theorems.FLT.Thm_WLight_levelN_structure_package
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelN_isDomain_ring

set_option autoImplicit false

open scoped MatrixGroups

theorem solution (M : ℕ) [NeZero M] : IsDomain (ModularCurve.LevelN.ring M) := by

  have hpkg := WLight.levelN_structure_package M PeriodPair.ofTau
    (fun τ => ⟨PeriodPair.ofTau_ω₁ τ, PeriodPair.ofTau_ω₂ τ⟩)
    (ModularCurve.LevelN.wp M) (fun v τ => rfl)
    (ModularCurve.LevelN.fricke M) (fun v τ => rfl)
    ModularCurve.LevelN.jAnalytic (fun τ => rfl)
  obtain ⟨-, -, -, -, -, hdom⟩ := hpkg

  have : NoZeroDivisors (ModularCurve.LevelN.ring M) := ⟨fun {a b} h => by
    have h' := hdom (a : UpperHalfPlane → ℂ) (b : UpperHalfPlane → ℂ) a.2 b.2
      (by simpa using congrArg Subtype.val h)
    rcases h' with ha | hb
    · left; exact Subtype.ext ha
    · right; exact Subtype.ext hb⟩
  have : Nontrivial (ModularCurve.LevelN.ring M) := inferInstance
  exact NoZeroDivisors.to_isDomain _

end S_ModularCurve_LevelN_isDomain_ring
end P2MW
export P2MW.S_ModularCurve_LevelN_isDomain_ring (solution)
