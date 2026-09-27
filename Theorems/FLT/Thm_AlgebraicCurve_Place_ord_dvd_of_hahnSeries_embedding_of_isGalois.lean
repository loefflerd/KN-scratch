import Mathlib
import Definitions.FLT.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.FLT.Def_HahnSeries_RamificationBound

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
theorem AlgebraicCurve.Place.ord_dvd_of_hahnSeries_embedding_of_isGalois
    {K L M : Type*} [Field K] [Field L] [Algebra K L] [Field M] [Algebra K M]
    [Algebra (RatFunc K) M] [IsScalarTower K (RatFunc K) M]
    [FiniteDimensional (RatFunc K) M] [IsGalois (RatFunc K) M]
    (p : Polynomial K) (hp : Irreducible p) (a : L)
    (ha : Polynomial.aeval a p = 0) (ha' : Polynomial.aeval a (Polynomial.derivative p) ≠ 0)
    (ψ : M →ₐ[K] HahnSeries ℚ L)
    (hψX : ψ (algebraMap (RatFunc K) M (algebraMap (Polynomial K) (RatFunc K) Polynomial.X))
      = HahnSeries.C a + HahnSeries.single (1 : ℚ) (1 : L))
    {d : ℕ} (hd : 0 < d) (hψ : ∀ m : M, HahnSeries.HasRamBound d (ψ m))
    (W : AlgebraicCurve.Place K M)
    (hW : 0 < W.ord (algebraMap (RatFunc K) M (algebraMap (Polynomial K) (RatFunc K) p))) :
    W.ord (algebraMap (RatFunc K) M (algebraMap (Polynomial K) (RatFunc K) p)) ∣ (d : ℤ) := by sorry
