import Mathlib
import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.FLT.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.FLT.Def_AlgebraicCurve_IsCurveOver
import Definitions.FLT.Def_ModularCurve_CanonicalDivisor
import Definitions.FLT.Def_ModularCurve_CanonicalDivisorUniformizer
import Definitions.FLT.Def_AlgebraicCurve_Repartitions
import Definitions.FLT.Def_AlgebraicCurve_AdelicIndex
import Definitions.FLT.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.FLT.Def_AlgebraicCurve_LocalResidue
import Definitions.FLT.Def_AlgebraicCurve_DivisorPushPull
import Definitions.FLT.Def_DedekindDomain_AdicValuation_InlineSpecific
import Definitions.FLT.Def_AlgebraicCurve_PlaceCompletion
import Definitions.FLT.Def_AlgebraicCurve_TateResidueCurrency
import Definitions.FLT.Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2
import Theorems.FLT.Thm_AlgebraicCurve_tateCommFinite
import Theorems.FLT.Thm_AlgebraicCurve_tateTraceCompat_of_isSeparable
import Theorems.FLT.Thm_AlgebraicCurve_tateAgreement
import Theorems.FLT.Thm_AlgebraicCurve_tateChainRule
import Definitions.FLT.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_residueTraceCompletionCommute
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option synthInstance.maxHeartbeats 6400000
set_option maxHeartbeats 12800000

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor HasPrincipalDivisors Pic0 IsCurveOver diagonalHom_apply HasCanonicalLocalResidueKStar kaehlerResidueTerm kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt tateCommFinite tateTraceCompat_of_isSeparable tateAgreement tateChainRule"
end AlgebraicCurve
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor HasPrincipalDivisors Pic0 IsCurveOver diagonalHom_apply HasCanonicalLocalResidueKStar kaehlerResidueTerm kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt tateCommFinite tateTraceCompat_of_isSeparable tateAgreement tateChainRule"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext FiniteResidue ord ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ne_top' toValuationSubring dCoord DCoordGenerates differentialCoeff uniformizer localResidue localResidue_eq_zero_of_ord_nonneg ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap adicCompletion adicCompletionIntegers"
end AlgebraicCurve.Place
namespace IntermediateField
p2m_export "IntermediateField" "toAlgebra val isIntegral_iff ext comap mem_top"
end IntermediateField
namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "HeightOneSpectrum"
end IsDedekindDomain
namespace IsDedekindDomain
p2m_export "IsDedekindDomain" "HeightOneSpectrum"
namespace HeightOneSpectrum
p2m_export "IsDedekindDomain.HeightOneSpectrum" "comap adicCompletion adicCompletionIntegers"
end IsDedekindDomain.HeightOneSpectrum
namespace IsLocalRing
end IsLocalRing
namespace KaehlerDifferential
p2m_export "KaehlerDifferential" "D"
end KaehlerDifferential
namespace LinearMap
p2m_export "LinearMap" "codRestrict inr ext isIntegral"
end LinearMap
namespace ModularCurve
p2m_export "ModularCurve" "KwF4gRRTate.KwF4gRRTateCommFinite KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute"
namespace KwF4R1V391a
p2m_export "ModularCurve.KwF4R1V391a" "KwF4R1V391aResidueTraceCompletionCommute"
end ModularCurve.KwF4R1V391a
namespace ModularCurve
p2m_export "ModularCurve" "KwF4gRRTate.KwF4gRRTateCommFinite KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute"
namespace KwF4gRRTate
p2m_export "ModularCurve.KwF4gRRTate" "KwF4gRRTateCommFinite KwF4gRRTateAgreement KwF4gRRTateChainRule KwF4gRRTateTraceCompat"
end ModularCurve.KwF4gRRTate
namespace ModularCurve
p2m_export "ModularCurve" "KwF4gRRTate.KwF4gRRTateCommFinite KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute"
namespace GF24a9RRDx
end ModularCurve.GF24a9RRDx
namespace Module
end Module
namespace MonoidWithZeroHom
p2m_export "MonoidWithZeroHom" "ext inr"
end MonoidWithZeroHom
namespace NNReal
p2m_export "NNReal" "coe_eq_zero"
end NNReal
namespace Pointwise
end Pointwise
namespace Polynomial
p2m_export "Polynomial" "ext_iff toSubring ext ring"
end Polynomial
namespace Submodule
p2m_export "Submodule" "mem_comap mem_top coe_eq_zero ext comap"
end Submodule
namespace Valuation
p2m_export "Valuation" "ext map_sub IsRankOneDiscrete comap"
namespace IsRankOneDiscrete
end Valuation.IsRankOneDiscrete
namespace Valued
p2m_export "Valued" "v"
end Valued
namespace WithZero
end WithZero
namespace WithZeroMulInt
end WithZeroMulInt

section
section

set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false

p2m_open "LinearMap P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.LinearMap Submodule P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.Submodule"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "KwF4gRRTate.KwF4gRRTateCommFinite KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute"
namespace KwF4gRRTate
p2m_export "ModularCurve.KwF4gRRTate" "KwF4gRRTateCommFinite KwF4gRRTateAgreement KwF4gRRTateChainRule KwF4gRRTateTraceCompat"
end ModularCurve.KwF4gRRTate

end

end

end

section
section

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.WithZero IsLocalRing P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor HasPrincipalDivisors Pic0 IsCurveOver diagonalHom_apply HasCanonicalLocalResidueKStar kaehlerResidueTerm kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt tateCommFinite tateTraceCompat_of_isSeparable tateAgreement tateChainRule"
p2m_open "AlgebraicCurve"

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace Place
p2m_export "AlgebraicCurve.Place" "ext FiniteResidue ord ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ne_top' toValuationSubring dCoord DCoordGenerates differentialCoeff uniformizer localResidue localResidue_eq_zero_of_ord_nonneg ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap adicCompletion adicCompletionIntegers"
end Place

namespace Divisor
end Divisor

namespace Pic0
end Pic0

namespace Place
p2m_export "AlgebraicCurve.Place" "ext FiniteResidue ord ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ne_top' toValuationSubring dCoord DCoordGenerates differentialCoeff uniformizer localResidue localResidue_eq_zero_of_ord_nonneg ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap adicCompletion adicCompletionIntegers"
end Place

namespace Divisor
end Divisor

namespace Pic0
end Pic0

namespace Place
p2m_export "AlgebraicCurve.Place" "ext FiniteResidue ord ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ne_top' toValuationSubring dCoord DCoordGenerates differentialCoeff uniformizer localResidue localResidue_eq_zero_of_ord_nonneg ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap adicCompletion adicCompletionIntegers"
end Place

end AlgebraicCurve

end
end

end

section
section

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.WithZero IsLocalRing P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor HasPrincipalDivisors Pic0 IsCurveOver diagonalHom_apply HasCanonicalLocalResidueKStar kaehlerResidueTerm kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt tateCommFinite tateTraceCompat_of_isSeparable tateAgreement tateChainRule"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext FiniteResidue ord ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ne_top' toValuationSubring dCoord DCoordGenerates differentialCoeff uniformizer localResidue localResidue_eq_zero_of_ord_nonneg ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap adicCompletion adicCompletionIntegers"
p2m_open "AlgebraicCurve.Place"

section SinglePlace

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

p2m_export "AlgebraicCurve.Place" "ord_nonneg_of_mem"
private theorem _root_.AlgebraicCurve.Place.mem_of_ord_nonneg {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

p2m_export "AlgebraicCurve.Place" "mem_of_ord_nonneg"
private theorem _root_.AlgebraicCurve.Place.mem_iff_ord_nonneg {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f :=
  ⟨v.ord_nonneg_of_mem, v.mem_of_ord_nonneg hf⟩

p2m_export "AlgebraicCurve.Place" "mem_iff_ord_nonneg"
theorem exists_ord_pos : ∃ f : F, f ≠ 0 ∧ 0 < v.ord f := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  refine ⟨(π : F), ?_, ?_⟩
  · simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  · rw [v.ord_coe_irreducible hπ]
    exact one_pos

end SinglePlace

section Restrict

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F'] [Algebra F F']

private theorem algebraMap_ne_zero {f : F} (hf : f ≠ 0) : algebraMap F F' f ≠ 0 := by
  simpa using hf

variable (w : Place K F')

private theorem _root_.AlgebraicCurve.Place.comap_algebraMap_ne_top [Algebra.IsIntegral F F'] :
    w.toValuationSubring.comap (algebraMap F F') ≠ ⊤ := by
  intro htop
  apply w.ne_top'
  have hF : ∀ f : F, algebraMap F F' f ∈ w.toValuationSubring := fun f =>
    ValuationSubring.mem_comap.mp (htop ▸ ValuationSubring.mem_top f)
  refine SetLike.ext fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => ?_⟩
  let : Algebra F w.toValuationSubring :=
    ((algebraMap F F').codRestrict w.toValuationSubring.toSubring hF).toAlgebra
  let : IsScalarTower F w.toValuationSubring F' :=
    IsScalarTower.of_algebraMap_eq fun f => rfl
  have hx : _root_.IsIntegral w.toValuationSubring x :=
    (Algebra.IsIntegral.isIntegral (R := F) x).tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx
  exact hy ▸ y.2

p2m_export "AlgebraicCurve.Place" "comap_algebraMap_ne_top"
variable {w} in

theorem mem_comap_iff_ord_nonneg {f : F} (hf : f ≠ 0) :
    f ∈ w.toValuationSubring.comap (algebraMap F F') ↔
      0 ≤ w.ord (algebraMap F F' f) := by
  rw [ValuationSubring.mem_comap]
  exact w.mem_iff_ord_nonneg (algebraMap_ne_zero hf)

variable {w} in

theorem isUnit_mk_comap_iff {f : F} (hf : f ≠ 0)
    (hmem : f ∈ w.toValuationSubring.comap (algebraMap F F')) :
    IsUnit (⟨f, hmem⟩ : w.toValuationSubring.comap (algebraMap F F')) ↔
      w.ord (algebraMap F F' f) = 0 := by
  constructor
  · rintro h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp h
    have hb' : f * (b : F) = 1 := by
      simpa [Subtype.ext_iff] using hb
    have hbne : (b : F) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hb'
      exact zero_ne_one hb'
    have hsum : w.ord (algebraMap F F' f) + w.ord (algebraMap F F' (b : F)) = 0 := by
      rw [← w.ord_mul (algebraMap_ne_zero hf) (algebraMap_ne_zero hbne), ← map_mul, hb',
        map_one, w.ord_one]
    have h1 : 0 ≤ w.ord (algebraMap F F' f) := (mem_comap_iff_ord_nonneg hf).mp hmem
    have h2 : 0 ≤ w.ord (algebraMap F F' (b : F)) := (mem_comap_iff_ord_nonneg hbne).mp b.2
    omega
  · intro h0
    have hinv : f⁻¹ ∈ w.toValuationSubring.comap (algebraMap F F') :=
      (mem_comap_iff_ord_nonneg (inv_ne_zero hf)).mpr (by rw [map_inv₀, w.ord_inv]; omega)
    exact ⟨⟨⟨f, hmem⟩, ⟨f⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hf),
      Subtype.ext (inv_mul_cancel₀ hf)⟩, rfl⟩

private theorem _root_.AlgebraicCurve.Place.exists_ord_algebraMap_pos [Algebra.IsIntegral F F'] :
    ∃ f : F, f ≠ 0 ∧ 0 < w.ord (algebraMap F F' f) := by
  have h := w.comap_algebraMap_ne_top (F := F)
  rw [ne_eq, SetLike.ext_iff, not_forall] at h
  obtain ⟨g, hg⟩ := h
  simp only [ValuationSubring.mem_top, iff_true] at hg
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hg (zero_mem _)
  refine ⟨g⁻¹, inv_ne_zero hg0, ?_⟩
  rw [map_inv₀, w.ord_inv]
  have := (mem_comap_iff_ord_nonneg hg0).not.mp hg
  omega

p2m_export "AlgebraicCurve.Place" "exists_ord_algebraMap_pos"
variable [Algebra.IsIntegral F F']

private theorem ramificationIndex_set_nonempty :
    {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ w.ord (algebraMap F F' f) = n}.Nonempty := by
  obtain ⟨f, hf0, hf⟩ := w.exists_ord_algebraMap_pos (F := F)
  exact ⟨(w.ord (algebraMap F F' f)).toNat, by omega, f, hf0, by omega⟩

theorem isPrincipalIdealRing_comap :
    IsPrincipalIdealRing (w.toValuationSubring.comap (algebraMap F F')) := by
  obtain ⟨g, hg0, hge⟩ := w.exists_ord_eq_ramificationIndex (F := F)
  have hepos : 0 < ramificationIndex (F := F) w := w.ramificationIndex_pos (F := F)
  have hgmem : g ∈ w.toValuationSubring.comap (algebraMap F F') :=
    (mem_comap_iff_ord_nonneg hg0).mpr (by omega)
  refine (IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨⟨g, hgmem⟩, irreducible_mk_comap w hg0 hgmem hge, ?_⟩).toIsPrincipalIdealRing
  rintro ⟨f, hmem⟩ hx
  have hf : f ≠ 0 := by simpa [Subtype.ext_iff] using hx
  obtain ⟨c, hc⟩ := w.ramificationIndex_dvd_ord (F := F) hf
  have hnonneg : 0 ≤ w.ord (algebraMap F F' f) := (mem_comap_iff_ord_nonneg hf).mp hmem
  have hcnonneg : 0 ≤ c := by
    by_contra hneg
    have hcle : c ≤ -1 := by omega
    have : (ramificationIndex (F := F) w : ℤ) * c ≤ (ramificationIndex (F := F) w : ℤ) * -1 :=
      mul_le_mul_of_nonneg_left hcle (by omega)
    omega
  set n : ℕ := c.toNat with hn
  have hcn : (n : ℤ) = c := Int.toNat_of_nonneg hcnonneg
  refine ⟨n, ?_⟩
  have hgn : g ^ n ≠ 0 := pow_ne_zero _ hg0
  have hdiv0 : f / g ^ n ≠ 0 := div_ne_zero hf hgn
  have hu0 : w.ord (algebraMap F F' (f / g ^ n)) = 0 := by
    have hkey : algebraMap F F' (f / g ^ n)
        = algebraMap F F' f * (algebraMap F F' g) ^ (-(n : ℤ)) := by
      rw [div_eq_mul_inv, map_mul, map_inv₀, map_pow, ← zpow_natCast (algebraMap F F' g) n,
        ← _root_.zpow_neg]
    rw [hkey, w.ord_mul (algebraMap_ne_zero hf) (zpow_ne_zero _ (algebraMap_ne_zero hg0)),
      w.ord_zpow, hge, hc, ← hcn]
    ring
  have humem : f / g ^ n ∈ w.toValuationSubring.comap (algebraMap F F') :=
    (mem_comap_iff_ord_nonneg hdiv0).mpr (le_of_eq hu0.symm)
  have hu : IsUnit (⟨f / g ^ n, humem⟩ : w.toValuationSubring.comap (algebraMap F F')) :=
    (isUnit_mk_comap_iff hdiv0 humem).mpr hu0
  refine ⟨hu.unit, ?_⟩
  refine Subtype.ext ?_
  have hcoe : ((hu.unit : w.toValuationSubring.comap (algebraMap F F')) : F) = f / g ^ n := by
    rw [IsUnit.unit_spec]
  push_cast
  rw [hcoe, mul_comm, div_mul_cancel₀]
  exact hgn

end Restrict

end Place

end AlgebraicCurve

end
end

end

section
section

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor HasPrincipalDivisors Pic0 IsCurveOver diagonalHom_apply HasCanonicalLocalResidueKStar kaehlerResidueTerm kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt tateCommFinite tateTraceCompat_of_isSeparable tateAgreement tateChainRule"
p2m_open "AlgebraicCurve"

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F']

namespace Place
p2m_export "AlgebraicCurve.Place" "ext FiniteResidue ord ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ne_top' toValuationSubring dCoord DCoordGenerates differentialCoeff uniformizer localResidue localResidue_eq_zero_of_ord_nonneg ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap adicCompletion adicCompletionIntegers"
end Place

namespace Divisor
end Divisor

namespace Divisor
end Divisor

end AlgebraicCurve

end
end

end

section
section

set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 6400000

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.IsDedekindDomain.HeightOneSpectrum IsLocalRing P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.IsLocalRing WithZero P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.WithZero MonoidWithZeroHom P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.MonoidWithZeroHom"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor HasPrincipalDivisors Pic0 IsCurveOver diagonalHom_apply HasCanonicalLocalResidueKStar kaehlerResidueTerm kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt tateCommFinite tateTraceCompat_of_isSeparable tateAgreement tateChainRule"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext FiniteResidue ord ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ne_top' toValuationSubring dCoord DCoordGenerates differentialCoeff uniformizer localResidue localResidue_eq_zero_of_ord_nonneg ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap adicCompletion adicCompletionIntegers"
end AlgebraicCurve.Place

end
end

end

section
section

set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 6400000

noncomputable section

p2m_open "Polynomial P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.Polynomial IsLocalRing P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.IsLocalRing IsDedekindDomain P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.IsDedekindDomain"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor HasPrincipalDivisors Pic0 IsCurveOver diagonalHom_apply HasCanonicalLocalResidueKStar kaehlerResidueTerm kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt tateCommFinite tateTraceCompat_of_isSeparable tateAgreement tateChainRule"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext FiniteResidue ord ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ne_top' toValuationSubring dCoord DCoordGenerates differentialCoeff uniformizer localResidue localResidue_eq_zero_of_ord_nonneg ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap adicCompletion adicCompletionIntegers"
end AlgebraicCurve.Place

end
end

end

section
section

set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 6400000

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.IsDedekindDomain IsDedekindDomain.HeightOneSpectrum P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.IsDedekindDomain.HeightOneSpectrum IsLocalRing P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.IsLocalRing WithZero P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.WithZero"

p2m_open_scoped "Valued P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.Valued WithZero P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.WithZero"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor HasPrincipalDivisors Pic0 IsCurveOver diagonalHom_apply HasCanonicalLocalResidueKStar kaehlerResidueTerm kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt tateCommFinite tateTraceCompat_of_isSeparable tateAgreement tateChainRule"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext FiniteResidue ord ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ne_top' toValuationSubring dCoord DCoordGenerates differentialCoeff uniformizer localResidue localResidue_eq_zero_of_ord_nonneg ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap adicCompletion adicCompletionIntegers"
end AlgebraicCurve.Place

end
end

end

section
section

noncomputable section

p2m_open "KaehlerDifferential P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.KaehlerDifferential"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor HasPrincipalDivisors Pic0 IsCurveOver diagonalHom_apply HasCanonicalLocalResidueKStar kaehlerResidueTerm kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt tateCommFinite tateTraceCompat_of_isSeparable tateAgreement tateChainRule"
p2m_open "AlgebraicCurve"

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace IsCurveOver
end IsCurveOver

namespace Place
p2m_export "AlgebraicCurve.Place" "ext FiniteResidue ord ord_one ord_mul ord_inv ord_coe_irreducible ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow ne_top' toValuationSubring dCoord DCoordGenerates differentialCoeff uniformizer localResidue localResidue_eq_zero_of_ord_nonneg ramificationIndex ramificationIndex_pos exists_ord_eq_ramificationIndex ramificationIndex_dvd_ord irreducible_mk_comap adicCompletion adicCompletionIntegers"
end Place

end AlgebraicCurve

namespace ModularCurve
p2m_export "ModularCurve" "KwF4gRRTate.KwF4gRRTateCommFinite KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute"
end ModularCurve

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor HasPrincipalDivisors Pic0 IsCurveOver diagonalHom_apply HasCanonicalLocalResidueKStar kaehlerResidueTerm kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt tateCommFinite tateTraceCompat_of_isSeparable tateAgreement tateChainRule"
end AlgebraicCurve

namespace ModularCurve
p2m_export "ModularCurve" "KwF4gRRTate.KwF4gRRTateCommFinite KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute"
end ModularCurve

end
end

end

section
section

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.WithZero"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor HasPrincipalDivisors Pic0 IsCurveOver diagonalHom_apply HasCanonicalLocalResidueKStar kaehlerResidueTerm kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt tateCommFinite tateTraceCompat_of_isSeparable tateAgreement tateChainRule"
end AlgebraicCurve

end

end

end

section
section

set_option linter.unusedSectionVars false

set_option synthInstance.maxHeartbeats 3200000
set_option maxHeartbeats 6400000

noncomputable section

p2m_open "IsDedekindDomain P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.IsDedekindDomain WithZero P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.WithZero Module P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.Module IsLocalRing P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.IsLocalRing Module.IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor HasPrincipalDivisors Pic0 IsCurveOver diagonalHom_apply HasCanonicalLocalResidueKStar kaehlerResidueTerm kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt tateCommFinite tateTraceCompat_of_isSeparable tateAgreement tateChainRule"
p2m_open "AlgebraicCurve"

section NoGoEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]

namespace FiberKaehlerLocalDatum

end FiberKaehlerLocalDatum

end NoGoEngine

end AlgebraicCurve

namespace ModularCurve
p2m_export "ModularCurve" "KwF4gRRTate.KwF4gRRTateCommFinite KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute"
p2m_open "ModularCurve"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.AlgebraicCurve Polynomial P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.Polynomial IntermediateField P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.IntermediateField"

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial

end ModularCurve

end

end

end

section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000
set_option linter.unusedSectionVars false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.AlgebraicCurve P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.ModularCurve.GF24a9RRDx AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.AlgebraicCurve.Place IsDedekindDomain P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.IsDedekindDomain"

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor HasPrincipalDivisors Pic0 IsCurveOver diagonalHom_apply HasCanonicalLocalResidueKStar kaehlerResidueTerm kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff kwHgfV352_exists_sub_mem_adicCompletionIntegers kaehlerPullback kwHgfV352_localResidueCompletion kwHgfV352_completionTraceAt tateCommFinite tateTraceCompat_of_isSeparable tateAgreement tateChainRule"
p2m_open "AlgebraicCurve"

section LocalResidueCompletion

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

variable [HasCanonicalLocalResidueKStar K E]

theorem kwHgfV352_localResidueCompletion_spec (v : Place K E) (xh : v.adicCompletion)
    {x : E} (hx : algebraMap E v.adicCompletion x - xh ∈ v.adicCompletionIntegers) :
    kwHgfV352_localResidueCompletion v xh = v.localResidue x := by
  unfold kwHgfV352_localResidueCompletion
  set x₀ := (kwHgfV352_exists_sub_mem_adicCompletionIntegers v xh).choose
  have hx₀ := (kwHgfV352_exists_sub_mem_adicCompletionIntegers v xh).choose_spec
  have heq : algebraMap E v.adicCompletion (x₀ - x)
      = (algebraMap E v.adicCompletion x₀ - xh) - (algebraMap E v.adicCompletion x - xh) := by
    rw [map_sub]; ring
  have hdiff : algebraMap E v.adicCompletion (x₀ - x) ∈ v.adicCompletionIntegers :=
    heq ▸ sub_mem hx₀ hx
  have hov : x₀ - x ∈ v.toValuationSubring :=
    (kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff v _).mp hdiff
  have hzero : v.localResidue (x₀ - x) = 0 :=
    v.localResidue_eq_zero_of_ord_nonneg (Or.inr (v.ord_nonneg_of_mem hov))
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

theorem kwHgfV352_localResidueCompletion_algebraMap (v : Place K E) (x : E) :
    kwHgfV352_localResidueCompletion v (algebraMap E v.adicCompletion x)
      = v.localResidue x :=
  kwHgfV352_localResidueCompletion_spec v _
    (by rw [sub_self]; exact zero_mem _)

end LocalResidueCompletion

end AlgebraicCurve

end
end

end

section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000
set_option linter.unusedSectionVars false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.AlgebraicCurve AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.AlgebraicCurve.Place LinearMap P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.LinearMap Submodule P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.Submodule"
p2m_open "ModularCurve.KwF4gRRTate P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.ModularCurve.KwF4gRRTate"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "KwF4gRRTate.KwF4gRRTateCommFinite KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute"
namespace KwF4gRRTate
p2m_export "ModularCurve.KwF4gRRTate" "KwF4gRRTateCommFinite KwF4gRRTateAgreement KwF4gRRTateChainRule KwF4gRRTateTraceCompat"
end ModularCurve.KwF4gRRTate

end

end

end

section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000
set_option linter.unusedSectionVars false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.AlgebraicCurve AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.AlgebraicCurve.Place P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.ModularCurve.GF24a9RRDx"
p2m_open "ModularCurve.KwF4R1V391a P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.ModularCurve.KwF4R1V391a ModularCurve.KwF4gRRTate P2MW.S_AlgebraicCurve_residueTraceCompletionCommute.ModularCurve.KwF4gRRTate"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "KwF4gRRTate.KwF4gRRTateCommFinite KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute"
namespace KwF4gRRTate
p2m_export "ModularCurve.KwF4gRRTate" "KwF4gRRTateCommFinite KwF4gRRTateAgreement KwF4gRRTateChainRule KwF4gRRTateTraceCompat"
p2m_open "ModularCurve.KwF4gRRTate ModularCurve"

section Wire

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]

theorem kwF4gRRTate_RTCC_of_tate
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    [Nontrivial Ω[F⁄K]] [∀ w : Place K F, w.DCoordGenerates]
    [∀ u : Place K E, u.FiniteResidue]
    (hfinF : KwF4gRRTateCommFinite K F) (hfinE : KwF4gRRTateCommFinite K E)
    (hAF : KwF4gRRTateAgreement K F hfinF) (hAE : KwF4gRRTateAgreement K E hfinE)
    (hC : KwF4gRRTateChainRule K F E hfinF)
    (hT : KwF4gRRTateTraceCompat K F E hfinF hfinE) :
    KwF4R1V391aResidueTraceCompletionCommute K F E := by
  intro _ _ _ v _ w _ hw g
  unfold kaehlerResidueTerm
  rw [diagonalHom_apply]
  rw [← kwHgfV352_localResidueCompletion_algebraMap w
    (g * w.differentialCoeff (kaehlerPullback K F E v.dCoord))]
  have := hfinF w (algebraMap F w.adicCompletion
    (g * w.differentialCoeff (kaehlerPullback K F E v.dCoord)))
    (algebraMap F w.adicCompletion w.uniformizer)
  rw [← hAF w (algebraMap F w.adicCompletion
    (g * w.differentialCoeff (kaehlerPullback K F E v.dCoord)))]
  rw [map_mul]
  have := hfinF w (algebraMap F w.adicCompletion g)
    (algebraMap F w.adicCompletion (algebraMap E F v.uniformizer))
  rw [← hC v w hw (algebraMap F w.adicCompletion g)]
  have := hfinE v (kwHgfV352_completionTraceAt v w hw g)
    (algebraMap E v.adicCompletion v.uniformizer)
  rw [hT v w hw g]
  rw [hAE v (kwHgfV352_completionTraceAt v w hw g)]

end Wire

end ModularCurve.KwF4gRRTate

end

end

end

theorem solution
    {K F E : Type*} [Field K] [Field F] [Algebra K F]
    [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
    [Algebra.IsIntegral E F]
    [∀ u : AlgebraicCurve.Place K E, u.FiniteResidue]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K E] [PerfectField K]
    [Nontrivial Ω[F⁄K]] [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    [Algebra.IsSeparable E F] :
    ModularCurve.KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute K F E :=
  let hF : ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K F := AlgebraicCurve.tateCommFinite
  let hE : ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K E := AlgebraicCurve.tateCommFinite
  ModularCurve.KwF4gRRTate.kwF4gRRTate_RTCC_of_tate hF hE
    (AlgebraicCurve.tateAgreement hF) (AlgebraicCurve.tateAgreement hE)
    (AlgebraicCurve.tateChainRule hF) (AlgebraicCurve.tateTraceCompat_of_isSeparable hF hE)

end S_AlgebraicCurve_residueTraceCompletionCommute
end P2MW
export P2MW.S_AlgebraicCurve_residueTraceCompletionCommute (solution)
