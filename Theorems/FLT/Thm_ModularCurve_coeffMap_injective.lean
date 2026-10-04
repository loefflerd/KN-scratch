module

public import Definitions.FLT.Def_ModularCurve_LaurentCoeff

import Definitions.FLT.Def_P2M_Util

section privateSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeffMap_injective

open ModularCurve IntermediateField HahnSeries

theorem solution {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S} (hf : Function.Injective f) : Function.Injective (ModularCurve.coeffMap f) :=
  fun x y hxy => by
  ext k
  exact hf (by simpa using congrArg (fun z => HahnSeries.coeff z k) hxy)

end S_ModularCurve_coeffMap_injective
end P2MW
export P2MW.S_ModularCurve_coeffMap_injective (solution)

end privateSection

public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem ModularCurve.coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S} (hf : Function.Injective f) : Function.Injective (ModularCurve.coeffMap f) := _root_.P2MW.S_ModularCurve_coeffMap_injective.solution hf

end publicSection
