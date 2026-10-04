import Definitions.FLT.Def_Gamma0CoeffCohomology
import Definitions.FLT.Def_HeckeEis_BinaryFormRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups
theorem HeckeEis.exists_coeffH1par_map_ringHom {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') (n : ℕ)
    (Γ : Subgroup SL(2, ℤ)) :
    ∃ Φ : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL R n).comp Γ.subtype) →+ HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL R' n).comp Γ.subtype),
      ∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL R n).comp Γ.subtype)),
      ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL R' n).comp Γ.subtype)),
        (∀ g : Γ, ((w : Γ → ↥(HeckeEis.BinaryForm R' n)) g : MvPolynomial (Fin 2) R')
            = MvPolynomial.map φ
                (((z : Γ → ↥(HeckeEis.BinaryForm R n)) g : MvPolynomial (Fin 2) R))) ∧
        Φ (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w := by sorry
