import Definitions.KN.Def_KN_EigenformResidualGaloisRepresentationV2

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- **This is a formalization of a standard textbook result, so should be
low-priority.**

Deligne's residual Galois representation attached to a normalized
eigenform and a chosen `p`-adic embedding.  Its coefficient field is
`f.coefficientField`, its prime is the canonically defined
`f.coefficientPrime ιp`, and its target is the resulting finite residue field
`EigenformResidueField f ιp`; none of these are auxiliary choices in
the existence statement. -/
theorem eigenform_residualGaloisRepresentation_exists_v2
    {N k p : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (ιp : MTT.Qbar →+* ℂ_[p]) :
    Nonempty (EigenformResidualGaloisRepresentationData hN hk f ιp) := by sorry

end HorizontalPadicL
