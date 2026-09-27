import Definitions.KN.Def_KN_SeededPrimeGaloisDataV2

set_option autoImplicit false

namespace HorizontalPadicL

theorem seededEigenform_padicPlace_exists_v2
    {N k p : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (hnew : IsNewEigenform f) (η : DirichletCharacterWithLevel) :
    Nonempty (SeededEigenformPadicPlaceData (p := p) f η) := by sorry

end HorizontalPadicL
