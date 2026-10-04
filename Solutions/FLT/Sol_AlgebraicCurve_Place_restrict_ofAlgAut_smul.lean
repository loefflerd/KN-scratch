import Definitions.FLT.Def_AlgebraicCurve_DivisorPushPull
import Definitions.FLT.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_restrict_ofAlgAut_smul

set_option autoImplicit false
noncomputable section
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_restrict_ofAlgAut_smul.AlgebraicCurve IsDedekindDomain"
open scoped Pointwise

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext SemilinearAut SemilinearAut.inv_smul_def SemilinearAut.ofAlgAut SemilinearAut.toRingAut_ofAlgAut SemilinearAut.smul_toValuationSubring"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "restrict restrict_toValuationSubring ext smul_toValuationSubring"
p2m_open "AlgebraicCurve.Place"

end Place
end AlgebraicCurve

open _root_.AlgebraicCurve.Place _root_.P2MW.S_AlgebraicCurve_Place_restrict_ofAlgAut_smul.AlgebraicCurve.Place in
theorem solution {K F' M : Type*} [Field K] [Field F'] [Field M]
    [Algebra K F'] [Algebra K M] [Algebra F' M] [IsScalarTower K F' M]
    [Algebra.IsIntegral F' M] (σ : M ≃ₐ[F'] M) (W : Place K M) :
    (SemilinearAut.ofAlgAut (σ.restrictScalars K) • W).restrict F' = W.restrict F' := by
  refine Place.ext ?_
  ext x
  rw [restrict_toValuationSubring, restrict_toValuationSubring, ValuationSubring.mem_comap,
    ValuationSubring.mem_comap, SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, SemilinearAut.inv_smul_def,
    SemilinearAut.toRingAut_ofAlgAut]
  have : ((σ.restrictScalars K : M ≃+* M).symm (algebraMap F' M x)) = algebraMap F' M x := by
    rw [RingEquiv.symm_apply_eq]
    exact (σ.commutes x).symm
  rw [this]

end

end S_AlgebraicCurve_Place_restrict_ofAlgAut_smul
end P2MW
export P2MW.S_AlgebraicCurve_Place_restrict_ofAlgAut_smul (solution)
