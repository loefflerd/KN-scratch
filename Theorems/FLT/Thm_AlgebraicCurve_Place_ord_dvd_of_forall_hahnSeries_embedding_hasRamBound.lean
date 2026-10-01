import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.HahnSeries.PowerSeries
import Mathlib.RingTheory.SimpleRing.Principal

import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.FLT.Def_HahnSeries_RamificationBound

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem AlgebraicCurve.Place.ord_dvd_of_forall_hahnSeries_embedding_hasRamBound
    {K L F : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] [IsAlgClosed L]
    [Field F] [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F]
    (p : Polynomial K) (hp : Irreducible p) (a : L)
    (ha : Polynomial.aeval a p = 0) (ha' : Polynomial.aeval a (Polynomial.derivative p) ≠ 0)
    {d : ℕ} (hd : 0 < d)
    (hF : ∀ ψ : F →ₐ[K] HahnSeries ℚ L,
      ψ (algebraMap (RatFunc K) F (algebraMap (Polynomial K) (RatFunc K) Polynomial.X))
          = HahnSeries.C a + HahnSeries.single (1 : ℚ) (1 : L) →
        ∀ x : F, HahnSeries.HasRamBound d (ψ x))
    (w : AlgebraicCurve.Place K F)
    (hw : 0 < w.ord (algebraMap (RatFunc K) F (algebraMap (Polynomial K) (RatFunc K) p))) :
    w.ord (algebraMap (RatFunc K) F (algebraMap (Polynomial K) (RatFunc K) p)) ∣ (d : ℤ) := by sorry
