import Definitions.KN.Def_KN_HorizontalPadicL
import Definitions.FLT.Def_FLTPrelim_Modularity

namespace HorizontalPadicL

/-- The q-expansion attached to an elliptic curve satisfies the normalized Hecke-eigenform
coefficient relations.  Concretely, this consists of `a₁ = 1`, multiplicativity at
coprime indices, and the good- and bad-prime recurrences for prime powers. -/
theorem ellipticCurve_attachedForm_isNormalizedEigenform
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (hmod : IsModular E) :
    CuspForm.IsNormalizedEigenform (modularFormAtConductor E hmod).form := by sorry

end HorizontalPadicL
