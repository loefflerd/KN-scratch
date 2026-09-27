import Definitions.KN.Def_KN_SeededPrimeGaloisDataV2

set_option autoImplicit false

namespace HorizontalPadicL

theorem newEigenform_residualRepresentation_exists_v2
    {N k p : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (hnew : IsNewEigenform f) (η : DirichletCharacterWithLevel)
    (V : SeededEigenformPadicPlaceData (p := p) f η) :
    Nonempty (ResidualEigenformRepresentationData f η V) := by sorry

end HorizontalPadicL
