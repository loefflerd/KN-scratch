import Definitions.FLT.Def_Gamma0CoeffCohomology
import Definitions.FLT.Def_HeckeEis_BinaryFormRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
theorem HeckeEis.coeffH1par_map_heckeT_comm {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') (n N ℓ : ℕ) [NeZero ℓ]
    (Φ : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype) →+ HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL R' n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hΦ : ∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
      ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL R' n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        (∀ g : CongruenceSubgroup.Gamma0 N, ((w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm R' n)) g : MvPolynomial (Fin 2) R')
            = MvPolynomial.map φ (((z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm R n)) g : MvPolynomial (Fin 2) R))) ∧
        Φ (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w)
    (T : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype) →ₗ[R] HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hT : ∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
      ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        (w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm R n)) = HeckeEis.coeffHeckeFun N ℓ ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype) (HeckeEis.binaryFormAlphaAdj R n ℓ) z ∧
        T (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w)
    (T' : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL R' n).comp (CongruenceSubgroup.Gamma0 N).subtype) →ₗ[R'] HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL R' n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hT' : ∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL R' n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
      ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL R' n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        (w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm R' n)) = HeckeEis.coeffHeckeFun N ℓ ((HeckeEis.binaryFormRepSL R' n).comp (CongruenceSubgroup.Gamma0 N).subtype) (HeckeEis.binaryFormAlphaAdj R' n ℓ) z ∧
        T' (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w)
    (x : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype)) :
    T' (Φ x) = Φ (T x) := by sorry
