import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_KaehlerDifferential_span_D_eq_top_of_transcendental

noncomputable section
p2m_open "Polynomial KaehlerDifferential P2MW.S_KaehlerDifferential_span_D_eq_top_of_transcendental.KaehlerDifferential"

namespace KaehlerDifferential
p2m_export "KaehlerDifferential" "tensorKaehlerEquivOfFormallyEtale polynomialEquiv tensorKaehlerEquivOfFormallyEtale_apply mapBaseChange_tmul D map_D map"
namespace FF2
p2m_open "KaehlerDifferential"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {x : F} (hx : Transcendental K x)
  [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F]

include hx in

private theorem exists_basis : ∃ b : Module.Basis Unit F Ω[F⁄K], b () = D K F x := by

  let e : RatFunc K ≃ₐ[K] IntermediateField.adjoin K ({x} : Set F) := RatFunc.algEquivOfTranscendental x hx
  let algKx : Algebra K[X] (IntermediateField.adjoin K ({x} : Set F)) := (e.toAlgHom.toRingHom.comp (algebraMap K[X] (RatFunc K))).toAlgebra
  let algF : Algebra K[X] F := ((algebraMap (IntermediateField.adjoin K ({x} : Set F)) F).comp (algebraMap K[X] (IntermediateField.adjoin K ({x} : Set F)))).toAlgebra
  have : IsScalarTower K[X] (IntermediateField.adjoin K ({x} : Set F)) F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower K K[X] (IntermediateField.adjoin K ({x} : Set F)) := IsScalarTower.of_algebraMap_eq (fun c => by
    change _ = (e.toAlgHom.toRingHom.comp (algebraMap K[X] (RatFunc K))) (C c)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_toAlgHom]
    rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply K K[X] (RatFunc K), AlgEquiv.commutes])
  have : IsScalarTower K K[X] F := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [IsScalarTower.algebraMap_apply K (IntermediateField.adjoin K ({x} : Set F)) F, IsScalarTower.algebraMap_apply K[X] (IntermediateField.adjoin K ({x} : Set F)) F,
      ← IsScalarTower.algebraMap_apply K K[X] (IntermediateField.adjoin K ({x} : Set F))])

  have : Algebra.FormallyEtale K[X] (RatFunc K) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors K[X])
  have : Algebra.FormallyEtale K[X] (IntermediateField.adjoin K ({x} : Set F)) :=
    Algebra.FormallyEtale.of_equiv (R := K[X]) (A := RatFunc K) { e with commutes' := fun _ => rfl }
  have : Algebra.FormallyEtale (IntermediateField.adjoin K ({x} : Set F)) F := Algebra.FormallyEtale.of_isSeparable (IntermediateField.adjoin K ({x} : Set F)) F
  have : Algebra.FormallyEtale K[X] F := Algebra.FormallyEtale.comp K[X] (IntermediateField.adjoin K ({x} : Set F)) F

  let b₀ : Module.Basis Unit K[X] Ω[K[X]⁄K] :=
    (Module.Basis.singleton Unit K[X]).map (polynomialEquiv K).symm
  have hb₀ : b₀ () = D K K[X] X := by simp [b₀]
  let ψ := tensorKaehlerEquivOfFormallyEtale K K[X] F
  refine ⟨(b₀.baseChange F).map ψ, ?_⟩
  have hX : algebraMap K[X] F X = x := by
    change algebraMap (IntermediateField.adjoin K ({x} : Set F)) F (e (algebraMap K[X] (RatFunc K) X)) = x
    rw [RatFunc.algebraMap_X]
    exact RatFunc.algEquivOfTranscendental_X x hx
  simp only [Module.Basis.map_apply, Module.Basis.baseChange_apply, hb₀, ψ,
    tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul, map_D, hX]

end KaehlerDifferential.FF2

theorem solution (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] (x : F) (hx : Transcendental K x)
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F] :
    Submodule.span F ({KaehlerDifferential.D K F x} : Set (KaehlerDifferential K F)) = ⊤ := by
  obtain ⟨b, hb⟩ := KaehlerDifferential.FF2.exists_basis hx
  have h := b.span_eq
  rwa [show Set.range b = {KaehlerDifferential.D K F x} by ext ω; simp [Set.range_unique, hb]] at h

end

end S_KaehlerDifferential_span_D_eq_top_of_transcendental
end P2MW
export P2MW.S_KaehlerDifferential_span_D_eq_top_of_transcendental (solution)
