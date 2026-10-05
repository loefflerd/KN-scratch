module

public import Definitions.KN.Def_KN_HorizontalPadicL

public section publicSection

namespace HorizontalPadicL

/-- Friedberg--Hoffstein nonvanishing with finite conductor avoidance, allowing
either parity of the primitive quadratic character. -/
theorem friedberg_hoffstein_quadratic_twist_nonzero_anyParity_v2
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (heven : Even k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (d : ℕ) (hd : 0 < d) :
    ∃ η : DirichletCharacterWithLevel,
      η.2.IsPrimitive ∧
      orderOf η.2 = 2 ∧
      Nat.Coprime (N * d) η.2.conductor ∧
      @MTT.criticalLValue ι f.form
        η.1.1 ⟨Nat.ne_of_gt η.1.2⟩ η.2 (k / 2 - 1) ≠ 0 := by sorry

end HorizontalPadicL

end publicSection
