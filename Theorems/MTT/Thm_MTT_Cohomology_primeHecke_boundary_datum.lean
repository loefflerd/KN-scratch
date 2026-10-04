import Definitions.MTT.Def_MTT_Cohomology_Boundary
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem MTT.Cohomology.primeHecke_boundary_datum
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) (e : DirichletCharacter ℂ N)
    (Φ : Cusp → Binary ℂ) (hΦ : IsBoundaryDatum N (k-2) Φ)
    (hlaw : ∀ γ : CongruenceSubgroup.Gamma0 N, ∀ x y,
      boundaryCochain Φ (cuspAct γ.val x, cuspAct γ.val y) =
        e (γ.val 1 1 : ZMod N) • act γ.val.val (boundaryCochain Φ (x, y)))
    (l : ℕ) (hl : l.Prime) :
    ∃ Ψ : Cusp → Binary ℂ, IsBoundaryDatum N (k-2) Ψ ∧
      primeHecke (e (l : ZMod N)) l (boundaryCochain Φ) = boundaryCochain Ψ := by sorry
