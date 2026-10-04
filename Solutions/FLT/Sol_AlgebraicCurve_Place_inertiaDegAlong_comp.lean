import Definitions.FLT.Def_AlgebraicCurve_Correspondence
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_inertiaDegAlong_comp

set_option autoImplicit false

open IsDedekindDomain AlgebraicCurve

theorem solution {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'') (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral) (hχφ : (χ.comp φ).toRingHom.IsIntegral) (W : Place K F'') : W.inertiaDegAlong (χ.comp φ) hχφ = W.inertiaDegAlong χ hχ * (W.restrictAlong χ hχ).inertiaDegAlong φ hφ := by
  let iχ : Algebra F' F'' := algebraAlong χ
  have := isScalarTower_along χ
  have := isIntegral_along χ hχ
  let iφ : Algebra F F' := algebraAlong φ
  have := isScalarTower_along φ
  have := isIntegral_along φ hφ
  let w : Place K F' := W.restrict F'
  let v : Place K F := w.restrict F
  let iχφ : Algebra F F'' := algebraAlong (χ.comp φ)
  have := isScalarTower_along (χ.comp φ)
  have := isIntegral_along (χ.comp φ) hχφ
  let : Algebra v.ResidueField W.ResidueField := (Place.restrictResidueMap F W).toAlgebra
  have : IsScalarTower v.ResidueField w.ResidueField W.ResidueField := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    show Place.restrictResidueMap F W (IsLocalRing.residue _ a)
      = Place.restrictResidueMap F' W (Place.restrictResidueMap F w (IsLocalRing.residue _ a))
    rw [Place.restrictResidueMap_residue, Place.restrictResidueMap_residue,
      Place.restrictResidueMap_residue]
    exact congrArg _ (Subtype.ext rfl)
  show Module.finrank v.ResidueField W.ResidueField
    = Module.finrank w.ResidueField W.ResidueField * Module.finrank v.ResidueField w.ResidueField
  rw [mul_comm]
  exact (Module.finrank_mul_finrank v.ResidueField w.ResidueField W.ResidueField).symm

end S_AlgebraicCurve_Place_inertiaDegAlong_comp
end P2MW
export P2MW.S_AlgebraicCurve_Place_inertiaDegAlong_comp (solution)
