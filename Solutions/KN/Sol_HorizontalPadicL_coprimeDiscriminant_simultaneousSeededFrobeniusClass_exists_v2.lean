import Theorems.KN.Thm_NumberField_not_dvd_discr_sup_of_not_dvd_discr
import Theorems.KN.Thm_IsCyclotomicExtension_Rat_prime_dvd_discr_dvd_conductor
import Theorems.KN.Thm_HorizontalPadicL_coprimeRamification_productFrobeniusClass_exists_v2

noncomputable section

namespace HorizontalPadicL

theorem _root_.solution
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
    Nonempty (SeededOrderlyFrobeniusClassData f η m B V) := by
  refine coprimeRamification_productFrobeniusClass_exists_v2
    hN hk ι f η m B hB hηcoprime V D a ha hdiscr
      NumberField.not_dvd_discr_sup_of_not_dvd_discr
      ?_
  intro n hn K hK hcyclo l hl hldisc
  exact IsCyclotomicExtension.Rat.prime_dvd_discr_dvd_conductor
    n K hl hldisc

end HorizontalPadicL
