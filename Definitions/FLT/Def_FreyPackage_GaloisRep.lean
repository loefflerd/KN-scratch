module

public import Definitions.FLT.Def_FLTPrelim_FreyPackage
public import Definitions.FLT.Def_FLTPrelim_GaloisRep
public import Definitions.FLT.Def_EllipticCurve_FrobeniusTrace
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

@[expose] public section publicSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe r s v

namespace WeierstrassCurve.Affine.Point

open WeierstrassCurve

variable {R : Type r} {S : Type s} {K : Type v} [CommRing R] [CommRing S] [Field K]
  [DecidableEq K] {W' : Affine R} [Algebra R S] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K]

noncomputable def galoisRep (W' : Affine R) (n : ℕ) :
    (K ≃ₐ[S] K) →*
      (Submodule.torsionBy ℤ (W'⁄K).Point n) ≃ₗ[ZMod n] (Submodule.torsionBy ℤ (W'⁄K).Point n) :=
  DistribMulAction.toModuleAut (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n)

@[simp]
lemma galoisRep_apply {n : ℕ} (σ : K ≃ₐ[S] K) (P : Submodule.torsionBy ℤ (W'⁄K).Point n) :
    galoisRep W' n σ P = σ • P :=
  rfl

end WeierstrassCurve.Affine.Point

namespace FreyPackage

open WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine

noncomputable local instance instDecEqQbarRepresentation : DecidableEq (AlgebraicClosure ℚ) :=
  Classical.decEq _

noncomputable def freyGaloisRep (P : FreyPackage) :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
      (Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p) ≃ₗ[ZMod P.p]
        (Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p) :=
  galoisRep P.freyCurve P.p

end FreyPackage


end publicSection
