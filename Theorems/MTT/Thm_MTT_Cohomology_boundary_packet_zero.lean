import Definitions.MTT.Def_MTT_Cohomology_Boundary
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.boundary_packet_zero
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (Φ : Cusp → Binary ℂ) (hΦ : IsBoundaryDatum N (k-2) Φ)
    (hlaw : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      boundaryCochain Φ (cuspAct γ.val x, cuspAct γ.val y) =
        ι (f.epsilon (γ.val 1 1 : ZMod N)) • act γ.val.val (boundaryCochain Φ (x, y)))
    (hH : ∀ l : ℕ, l.Prime →
      primeHecke (ι (f.epsilon (l : ZMod N))) l (boundaryCochain Φ) =
        ι (f.coeff l) • boundaryCochain Φ) :
    boundaryCochain Φ = 0 := by sorry
