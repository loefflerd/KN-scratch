import Definitions.FLT.Def_HeckeGalois_EichlerShimura
import Definitions.FLT.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ModularCurve

def IsEigenformIdeal (N : ℕ) (𝔪 : Ideal HeckeAlg) : Prop :=
  ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (_ : f.IsNormalizedEigenform)
    (k : Type) (_ : Field k) (_ : Finite k) (𝒪 : Subring ℂ)
    (h𝒪 : ∀ ℓ : Nat.Primes, ModularFormClass.qCoeff f ℓ ∈ 𝒪) (φ : 𝒪 →+* k),
      𝔪 = eigenIdeal (fun ℓ => φ ⟨ModularFormClass.qCoeff f ℓ, h𝒪 ℓ⟩)

abbrev EigenformSupportAt (N p : ℕ) (J : Type*) [AddCommGroup J] [Module HeckeAlg J] : Prop :=
  EigenformSupport p J (IsEigenformIdeal N)

abbrev EichlerShimuraDataAt {K L : Type*} [Field K] [Field L] [Algebra K L] (N p : ℕ)
    (J : Type*) [AddCommGroup J] [Module HeckeAlg J] [DistribMulAction (L ≃ₐ[K] L) J] :
    Prop :=
  EichlerShimuraDataReduced (K := K) (L := L) N p J (IsEigenformIdeal N)

end ModularCurve

