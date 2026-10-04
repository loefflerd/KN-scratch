import Definitions.KN.Def_KN_SeededThetaConstructionV2B

noncomputable section

namespace HorizontalPadicL

/-- At positive level and classical weight, expanding `(mX+a)^j` identifies
`MTT.algebraicSymbol` with the signed classical modular symbol.  The modulus is
required to be nonzero, as in the modular-symbol construction. -/
theorem algebraicSymbol_eq_signedModularSymbol_v3
    {N k : ℕ} {ι : MTT.Qbar →+* ℂ}
    (hN : 0 < N) (hk : 2 ≤ k) (f : MTT.Eigenform N k ι)
    (P : MTT.Periods k ι f.form) (s : Bool) (j : ℕ) (a m : ℚ)
    (hj : j ≤ k - 2) (hm : m ≠ 0) :
    ι (MTT.algebraicSymbol P s j a m) * P.omega s =
      signedModularSymbol f.form s j a m := by
  sorry

end HorizontalPadicL
