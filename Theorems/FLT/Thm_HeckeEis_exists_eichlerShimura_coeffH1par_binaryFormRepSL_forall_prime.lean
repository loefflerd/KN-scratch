import Mathlib
import Definitions.FLT.Def_Gamma0HeckeOperatorHom
import Definitions.FLT.Def_Gamma0CoeffCohomology
import Definitions.FLT.Def_HeckeEis_BinaryFormRep
import Definitions.FLT.Def_ModularForm_HeckeOperatorForms
import Definitions.FLT.Def_CuspForm_HeckeAlgebra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups
theorem HeckeEis.exists_eichlerShimura_coeffH1par_binaryFormRepSL_forall_prime (N : ℕ) [NeZero N] (n : ℕ) :
    ∃ (ES : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2) →ₗ[ℂ]
          HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype))
      (ESbar : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2) →ₛₗ[starRingEnd ℂ]
          HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
      Function.Injective ES ∧ Function.Injective ESbar ∧
      IsCompl (LinearMap.range ES) (LinearMap.range ESbar) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
        (T : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) →ₗ[ℂ] HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        (∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
            ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
              haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
              (w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n))
                  = HeckeEis.coeffHeckeFun N ℓ ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) (HeckeEis.binaryFormAlphaAdj ℂ n ℓ) z ∧
                T (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w) →
        (∀ f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2),
            T (ES f) = ES (CuspForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN f)) ∧
        (∀ f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2),
            T (ESbar f) = ESbar (CuspForm.heckeTLin ((n : ℤ) + 2) hℓ hℓN f))) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N)
        (T : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) →ₗ[ℂ] HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        (∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
            ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
              haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
              (w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n))
                  = HeckeEis.coeffHeckeFun N ℓ ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) (HeckeEis.binaryFormAlphaAdj ℂ n ℓ) z ∧
                T (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w) →
        (∀ f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2),
            T (ES f) = ES (CuspForm.heckeULin ((n : ℤ) + 2) hℓN f)) ∧
        (∀ f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2),
            T (ESbar f) = ESbar (CuspForm.heckeULin ((n : ℤ) + 2) hℓN f))) := by sorry
