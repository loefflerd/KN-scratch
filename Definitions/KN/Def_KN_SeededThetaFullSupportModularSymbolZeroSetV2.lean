module

public import Definitions.KN.Def_KN_SeededThetaFullSupportInterpolationV3

@[expose] public section publicSection

noncomputable section
open scoped BigOperators

namespace HorizontalPadicL

/-- At characters which are primitive at the full selected support, evaluation
of the finite theta element has the same zero set as the complex modular-symbol
sum occurring in the Birch--Mellin formula for the product of the seed and the
realized horizontal character.  This isolates the finite theta construction
from the analytic Birch--Mellin calculation. -/
def SeededFiniteThetaDataV3.HasFullSupportModularSymbolZeroSet
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (Θ : SeededFiniteThetaDataV3 L) : Prop :=
  ∀ χ, (Θ.characters.realized χ).2.conductor = L.supportModulus χ.support →
    (Θ.eval χ ≠ 0 ↔
      let θ := primitiveProductV2 η (Θ.characters.realized χ)
      letI : NeZero θ.1.1 := ⟨Nat.ne_of_gt θ.1.2⟩
      (∑ a : ZMod θ.1.1,
        ι (θ.2 a) * MTT.modularSymbol f.form (k / 2 - 1) a.val θ.1.1) ≠ 0)

end HorizontalPadicL

end

end publicSection
