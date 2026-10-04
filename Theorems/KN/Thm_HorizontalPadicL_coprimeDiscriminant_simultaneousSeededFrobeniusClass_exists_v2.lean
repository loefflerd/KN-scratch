import Definitions.KN.Def_KN_SeededPrimeGaloisDataV2
import Definitions.KN.Def_KN_EigenformResidualGaloisRepresentationV2
import Mathlib.NumberTheory.NumberField.Discriminant.Different

noncomputable section

namespace HorizontalPadicL

/-- The pure Galois-theoretic step in the seeded-prime construction.

Suppose the kernel field of a residual eigenform representation has
discriminant supported on `N * p`, and choose a residue class on which the
seed character has full order.  If the seed conductor is coprime to `N * p`,
then the residual kernel field and the `p ^ m * N` cyclotomic field are
linearly disjoint from the seed cyclotomic field.  A product automorphism
which is trivial on the first two factors and realizes the chosen seed class
therefore determines the required Chebotarev class. -/
theorem coprimeDiscriminant_simultaneousSeededFrobeniusClass_exists_v2
    {N k p : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (η : DirichletCharacterWithLevel)
    (m B : ℕ) (hB : 0 < B)
    (hηcoprime : Nat.Coprime (N * p) η.2.conductor)
    (V : SeededEigenformPadicPlaceData (p := p) f η)
    (D : EigenformResidualGaloisRepresentationData hN hk f V.embedding)
    (a : (ZMod η.1.1)ˣ)
    (ha : orderOf (η.2 (a : ZMod η.1.1)) = orderOf η.2)
    (hdiscr :
      letI : Field D.kernelField := D.kernelField_field
      letI : NumberField D.kernelField := D.kernelField_numberField
      ∀ {l : ℕ}, l.Prime →
        (l : ℤ) ∣ NumberField.discr D.kernelField → l ∣ N * p) :
    Nonempty (SeededOrderlyFrobeniusClassData f η m B V) := by sorry

end HorizontalPadicL
